#define _FILE_OFFSET_BITS 64
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <inttypes.h>
#include <unistd.h>

#define BS 4096u
#define INODE_SIZE 128u
#define ROOT_INO 1u
#define DIRECT_MAX 12
#define MAGIC 0x4D565346u
#define VERSION 1u
#define MODE_FILE 0100000u
#define MODE_DIR  0040000u

/* Group/project ID */
#define GROUP_ID 3u

/* FS limits */
#define MIN_SIZE_KIB 180u
#define MAX_SIZE_KIB 4096u
#define MIN_INODES 128u
#define MAX_INODES 512u

#pragma pack(push,1)
typedef struct {
    uint32_t magic, version, block_size;
    uint64_t total_blocks, inode_count;
    uint64_t inode_bitmap_start, inode_bitmap_blocks;
    uint64_t data_bitmap_start, data_bitmap_blocks;
    uint64_t inode_table_start, inode_table_blocks;
    uint64_t data_region_start, data_region_blocks;
    uint64_t root_inode, mtime_epoch;
    uint32_t flags, checksum;
} superblock_t;
#pragma pack(pop)
_Static_assert(sizeof(superblock_t)==116,"superblock mismatch");

#pragma pack(push,1)
typedef struct {
    uint16_t mode;
    uint16_t links;
    uint32_t uid, gid;
    uint64_t size_bytes;
    uint64_t atime, mtime, ctime;
    uint32_t direct[DIRECT_MAX];
    uint32_t reserved_0, reserved_1, reserved_2;
    uint32_t proj_id, uid16_gid16;
    uint64_t xattr_ptr, inode_crc;
} inode_t;
#pragma pack(pop)
_Static_assert(sizeof(inode_t)==INODE_SIZE,"inode size mismatch");

#pragma pack(push,1)
typedef struct {
    uint32_t inode_no; uint8_t type;
    char name[58]; uint8_t checksum;
} dirent64_t;
#pragma pack(pop)
_Static_assert(sizeof(dirent64_t)==64,"dirent mismatch");

/* ---------- CRC32 ---------- */
static uint32_t CRC32_TAB[256];
static void crc32_init(void) {
    for(uint32_t i=0;i<256;i++){uint32_t c=i; for(int j=0;j<8;j++) c=(c&1)?(0xEDB88320u^(c>>1)):(c>>1); CRC32_TAB[i]=c;}
}
static uint32_t crc32(const void* data,size_t n){
    const uint8_t* p=(const uint8_t*)data; uint32_t c=0xFFFFFFFFu;
    for(size_t i=0;i<n;i++) c=CRC32_TAB[(c^p[i])&0xFF]^(c>>8);
    return c^0xFFFFFFFFu;
}
static void inode_crc_finalize(inode_t* ino){ uint8_t tmp[INODE_SIZE]; memcpy(tmp,ino,INODE_SIZE); memset(&tmp[120],0,8); ino->inode_crc=crc32(tmp,120);}
static void dirent_finalize(dirent64_t* de){ const uint8_t* p=(const uint8_t*)de; uint8_t x=0; for(int i=0;i<63;i++) x^=p[i]; de->checksum=x; }

/* ---------- Helpers ---------- */
static int write_block(FILE* fp, const void* buf){ return fwrite(buf,BS,1,fp)==1?0:-1; }
static void set_bit(uint8_t* bm,uint64_t i){ bm[i/8]|=(1u<<(i%8)); }

/* Layout calculation */
static int calc_layout(uint64_t size_kib,uint64_t inodes,uint64_t* total_blocks,uint64_t* inode_table_blocks,uint64_t* data_region_start,uint64_t* data_region_blocks){
    *total_blocks=(size_kib*1024ULL)/BS;
    *inode_table_blocks=((inodes*INODE_SIZE)+BS-1)/BS;
    *data_region_start=3+*inode_table_blocks;
    if(*data_region_start>=*total_blocks) return -1;
    *data_region_blocks=*total_blocks-*data_region_start;
    if(*data_region_blocks<1) return -1;
    return 0;
}

/* ---------- Writers ---------- */
static int write_superblock(FILE* fp,uint64_t total_blocks,uint64_t inode_count,uint64_t inode_table_blocks,uint64_t data_region_start,uint64_t data_region_blocks,time_t now){
    uint8_t blk[BS]; memset(blk,0,BS);
    superblock_t* sb=(superblock_t*)blk;
    sb->magic=MAGIC; sb->version=VERSION; sb->block_size=BS;
    sb->total_blocks=total_blocks; sb->inode_count=inode_count;
    sb->inode_bitmap_start=1; sb->inode_bitmap_blocks=1;
    sb->data_bitmap_start=2; sb->data_bitmap_blocks=1;
    sb->inode_table_start=3; sb->inode_table_blocks=inode_table_blocks;
    sb->data_region_start=data_region_start; sb->data_region_blocks=data_region_blocks;
    sb->root_inode=ROOT_INO; sb->mtime_epoch=(uint64_t)now; sb->flags=0; sb->checksum=0;
    sb->checksum=crc32(blk,BS-4);
    return write_block(fp,blk);
}

static int write_inode_bitmap(FILE* fp){ uint8_t blk[BS]={0}; set_bit(blk,0); return write_block(fp,blk);}
static int write_data_bitmap(FILE* fp){ uint8_t blk[BS]={0}; set_bit(blk,0); return write_block(fp,blk);}

static int write_inode_table(FILE* fp,uint64_t inode_table_blocks,uint64_t data_region_start,time_t now){
    uint64_t inode_idx=0;
    uint32_t inodes_per_block=(uint32_t)(BS/INODE_SIZE);
    for(uint64_t b=0;b<inode_table_blocks;b++){
        uint8_t blk[BS]={0};
        for(uint32_t slot=0;slot<inodes_per_block;slot++){
            if(inode_idx==0){
                inode_t* r=(inode_t*)(blk+slot*INODE_SIZE);
                memset(r,0,INODE_SIZE);
                r->mode=MODE_DIR; r->links=2; r->size_bytes=BS;
                r->atime=r->mtime=r->ctime=(uint64_t)now;
                r->proj_id=GROUP_ID;
                r->direct[0]=(uint32_t)data_region_start;
                inode_crc_finalize(r);
            }
            inode_idx++;
        }
        if(write_block(fp,blk)!=0) return -1;
    }
    return 0;
}

static int write_data_region(FILE* fp,uint64_t data_region_blocks){
    for(uint64_t i=0;i<data_region_blocks;i++){
        uint8_t blk[BS]={0};
        if(i==0){
            dirent64_t* d=(dirent64_t*)blk;
            memset(&d[0],0,sizeof(dirent64_t)); d[0].inode_no=ROOT_INO; d[0].type=2; strcpy(d[0].name,"."); dirent_finalize(&d[0]);
            memset(&d[1],0,sizeof(dirent64_t)); d[1].inode_no=ROOT_INO; d[1].type=2; strcpy(d[1].name,".."); dirent_finalize(&d[1]);
        }
        if(write_block(fp,blk)!=0) return -1;
    }
    return 0;
}

/* ---------- Main ---------- */
int main(int argc,char* argv[]){
    crc32_init();

    if(argc<7){ fprintf(stderr,"Usage: %s --image <img> --size-kib <180..4096> --inodes <128..512>\n",argv[0]); return 1; }

    const char* image_name=NULL; uint64_t size_kib=0,inodes=0;
    for(int i=1;i<argc;i++){
        if(strcmp(argv[i],"--image")==0 && i+1<argc) image_name=argv[++i];
        else if(strcmp(argv[i],"--size-kib")==0 && i+1<argc) size_kib=strtoull(argv[++i],NULL,10);
        else if(strcmp(argv[i],"--inodes")==0 && i+1<argc) inodes=strtoull(argv[++i],NULL,10);
        else { fprintf(stderr,"Unknown arg %s\n",argv[i]); return 1;}
    }

    if(!image_name){ fprintf(stderr,"Missing --image\n"); return 1;}
    if(size_kib<MIN_SIZE_KIB || size_kib>MAX_SIZE_KIB || (size_kib%4)!=0){ fprintf(stderr,"Invalid size\n"); return 1;}
    if(inodes<MIN_INODES || inodes>MAX_INODES){ fprintf(stderr,"Invalid inodes\n"); return 1;}

    uint64_t total_blocks,inode_table_blocks,data_region_start,data_region_blocks;
    if(calc_layout(size_kib,inodes,&total_blocks,&inode_table_blocks,&data_region_start,&data_region_blocks)!=0){ fprintf(stderr,"Insufficient space\n"); return 1;}

    FILE* fp=fopen(image_name,"wb"); if(!fp){ perror("fopen"); return 1; }
    time_t now=time(NULL); if(now==(time_t)-1) now=0;

    if(write_superblock(fp,total_blocks,inodes,inode_table_blocks,data_region_start,data_region_blocks,now)!=0 ||
       write_inode_bitmap(fp)!=0 ||
       write_data_bitmap(fp)!=0 ||
       write_inode_table(fp,inode_table_blocks,data_region_start,now)!=0 ||
       write_data_region(fp,data_region_blocks)!=0){ fclose(fp); unlink(image_name); return 1;}

    if(fclose(fp)!=0){ perror("fclose"); return 1; }

    printf("Created image '%s' (%" PRIu64 " KiB) with %" PRIu64 " inodes\n",image_name,size_kib,inodes);
    return 0;
}
