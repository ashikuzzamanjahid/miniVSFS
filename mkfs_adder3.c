#define _FILE_OFFSET_BITS 64
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <libgen.h>

#define BS 4096u
#define INODE_SIZE 128u
#define ROOT_INO 1u
#define DIRECT_MAX 12
#define MAGIC 0x4D565346u
#define VERSION 1u
#define MODE_FILE 0100000u

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
_Static_assert(sizeof(superblock_t) == 116, "superblock mismatch");

#pragma pack(push,1)
typedef struct {
    uint16_t mode, links;
    uint32_t uid, gid;
    uint64_t size_bytes, atime, mtime, ctime;
    uint32_t direct[DIRECT_MAX];
    uint32_t reserved_0, reserved_1, reserved_2;
    uint32_t proj_id;
    uint32_t uid16_gid16;
    uint64_t xattr_ptr, inode_crc;
} inode_t;
#pragma pack(pop)
_Static_assert(sizeof(inode_t) == INODE_SIZE, "inode size mismatch");

#pragma pack(push,1)
typedef struct {
    uint32_t inode_no;
    uint8_t type;
    char name[58];
    uint8_t checksum;
} dirent64_t;
#pragma pack(pop)
_Static_assert(sizeof(dirent64_t) == 64, "dirent mismatch");

// ===== CRC =====
uint32_t CRC32_TAB[256];
void crc32_init(void){
    for(uint32_t i=0;i<256;i++){
        uint32_t c=i;
        for(int j=0;j<8;j++) c=(c&1)?(0xEDB88320u^(c>>1)):(c>>1);
        CRC32_TAB[i]=c;
    }
}
uint32_t crc32(const void* data,size_t n){
    const uint8_t* p=data; uint32_t c=0xFFFFFFFFu;
    for(size_t i=0;i<n;i++) c=CRC32_TAB[(c^p[i])&0xFF]^(c>>8);
    return c^0xFFFFFFFFu;
}
void inode_crc_finalize(inode_t* ino){
    uint8_t tmp[INODE_SIZE];
    memcpy(tmp, ino, INODE_SIZE);
    memset(&tmp[120], 0, 8);
    ino->inode_crc = crc32(tmp, 120);
}
void dirent_finalize(dirent64_t* de){
    uint8_t x=0; for(int i=0;i<63;i++) x^=((uint8_t*)de)[i];
    de->checksum = x;
}

// ===== Helpers =====
static int get_free_bit(uint8_t* bm,uint64_t n){
    for(uint64_t i=0;i<n;i++) if(!(bm[i/8] & (1u << (i%8))) ) return i;
    return -1;
}
static void set_bit(uint8_t* bm,uint64_t i){ bm[i/8] |= (1u << (i%8)); }

// ===== Main =====
int main(int argc,char* argv[]){
    if(argc!=7){
        fprintf(stderr,"Usage: %s --input in.img --output out.img --file myfile\n",argv[0]);
        return 1;
    }

    const char *in=NULL, *out=NULL, *file=NULL;
    for(int i=1;i<argc;i+=2){
        if(!strcmp(argv[i],"--input")) in=argv[i+1];
        else if(!strcmp(argv[i],"--output")) out=argv[i+1];
        else if(!strcmp(argv[i],"--file")) file=argv[i+1];
    }
    if(!in||!out||!file){ fprintf(stderr,"Missing required arguments\n"); return 1; }

    crc32_init();

    // Read file to add
    FILE* f=fopen(file,"rb");
    if(!f){ perror("file open"); return 1; }
    fseek(f,0,SEEK_END); long fsize=ftell(f); rewind(f);
    uint8_t* fbuf=malloc(fsize);
    if(!fbuf){ perror("malloc"); fclose(f); return 1; }
    if(fread(fbuf,1,fsize,f)!=(size_t)fsize){ perror("fread"); free(fbuf); fclose(f); return 1; }
    fclose(f);

    // Read input image
    FILE* fi=fopen(in,"rb");
    if(!fi){ perror("input image"); free(fbuf); return 1; }
    fseek(fi,0,SEEK_END); long isz=ftell(fi); rewind(fi);
    uint8_t* img=malloc(isz);
    if(!img){ perror("malloc image"); fclose(fi); free(fbuf); return 1; }
    if(fread(img,1,isz,fi)!=(size_t)isz){ perror("fread image"); free(fbuf); free(img); fclose(fi); return 1; }
    fclose(fi);

    // Map FS structures
    superblock_t* sb=(superblock_t*)img;
    if(sb->magic!=MAGIC || sb->version!=VERSION || sb->block_size!=BS){
        fprintf(stderr,"Invalid filesystem image\n"); free(fbuf); free(img); return 1;
    }

    uint8_t* ibm=img+sb->inode_bitmap_start*BS;
    uint8_t* dbm=img+sb->data_bitmap_start*BS;
    inode_t* inodes=(inode_t*)(img+sb->inode_table_start*BS);
    uint8_t* data=img+sb->data_region_start*BS;

    // Allocate inode
    int ino_idx=get_free_bit(ibm,sb->inode_count);
    if(ino_idx<0){ fprintf(stderr,"No free inodes\n"); free(fbuf); free(img); return 1; }
    set_bit(ibm,ino_idx);

    // Allocate data blocks
    int blocks=(fsize+BS-1)/BS; int db[DIRECT_MAX], cnt=0;
    for(uint64_t b=0;b<sb->data_region_blocks && cnt<blocks;b++){
        if(!(dbm[b/8] & (1u<<(b%8)))){ db[cnt++]=b; set_bit(dbm,b); }
    }
    if(cnt<blocks){ fprintf(stderr,"Not enough free blocks\n"); free(fbuf); free(img); return 1; }

    // Init inode
    inode_t* ino=&inodes[ino_idx]; memset(ino,0,INODE_SIZE);
    ino->mode=MODE_FILE; ino->links=1; ino->size_bytes=fsize;
    ino->atime=ino->mtime=ino->ctime=time(NULL);
    ino->proj_id=3;
    for(int i=0;i<blocks;i++) ino->direct[i]=sb->data_region_start+db[i];
    inode_crc_finalize(ino);

    // Copy file content
    size_t offset=0, remaining=fsize;
    for(int i=0;i<blocks;i++){
        size_t sz=remaining<BS?remaining:BS;
        memcpy(data+db[i]*BS,fbuf+offset,sz);
        if(sz<BS) memset(data+db[i]*BS+sz,0,BS-sz);
        offset+=sz; remaining-=sz;
    }

    // Add directory entry
    inode_t* root=&inodes[0];
    dirent64_t* ents=(dirent64_t*)(data+(root->direct[0]-sb->data_region_start)*BS);
    char* base=basename((char*)file);
    for(size_t i=0; i<BS/sizeof(dirent64_t); i++){
    if(ents[i].inode_no==0){
        ents[i].inode_no=ino_idx+1;
        ents[i].type=1;
        strncpy(ents[i].name, base, sizeof(ents[i].name)-1);
        dirent_finalize(&ents[i]);
        break;
    }
}


    // Write back updated image
    FILE* fo=fopen(out,"wb");
    if(!fo){ perror("output image"); free(fbuf); free(img); return 1; }
    if(fwrite(img,1,isz,fo)!=(size_t)isz){ perror("write"); fclose(fo); free(fbuf); free(img); return 1; }
    fclose(fo);

    printf("Added %s -> %s\n", file, out);

    free(fbuf); free(img);
    return 0;
}
