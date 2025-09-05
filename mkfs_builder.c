// Build: gcc -O2 -std=c17 -Wall -Wextra -Werror mkfs_builder.c -o mkfs_builder
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
#define DIRENT_SIZE 64u
#define ROOT_INO 1u
#define DIRECT_MAX 12
#define MAGIC 0x4D565346u
#define VERSION 1u

/* Adjust your group/project id here if required by grader */
#define GROUP_ID 3u

/* Limits from spec */
#define MIN_SIZE_KIB 180u
#define MAX_SIZE_KIB 4096u
#define MIN_INODES 128u
#define MAX_INODES 512u

/* Modes */
#define MODE_FILE 0100000u
#define MODE_DIR  0040000u

#pragma pack(push, 1)
typedef struct {
    uint32_t magic;               // 4
    uint32_t version;             // 4
    uint32_t block_size;          // 4
    uint64_t total_blocks;        // 8
    uint64_t inode_count;         // 8
    uint64_t inode_bitmap_start;  // 8
    uint64_t inode_bitmap_blocks; // 8
    uint64_t data_bitmap_start;   // 8
    uint64_t data_bitmap_blocks;  // 8
    uint64_t inode_table_start;   // 8
    uint64_t inode_table_blocks;  // 8
    uint64_t data_region_start;   // 8
    uint64_t data_region_blocks;  // 8
    uint64_t root_inode;          // 8
    uint64_t mtime_epoch;         // 8
    uint32_t flags;               // 4
    uint32_t checksum;            // 4 (CRC32 of block[0..4091])
} superblock_t;
#pragma pack(pop)
_Static_assert(sizeof(superblock_t) == 116, "superblock must be 116 bytes");

#pragma pack(push, 1)
typedef struct {
    uint16_t mode;            // 2
    uint16_t links;           // 2
    uint32_t uid;             // 4
    uint32_t gid;             // 4
    uint64_t size_bytes;      // 8
    uint64_t atime;           // 8
    uint64_t mtime;           // 8
    uint64_t ctime;           // 8
    uint32_t direct[DIRECT_MAX]; // 48
    uint32_t reserved_0;      // 4
    uint32_t reserved_1;      // 4
    uint32_t reserved_2;      // 4
    uint32_t proj_id;         // 4
    uint32_t uid16_gid16;     // 4
    uint64_t xattr_ptr;       // 8
    uint64_t inode_crc;       // 8 (lower 32 bits = crc32 of bytes [0..119])
} inode_t;
#pragma pack(pop)
_Static_assert(sizeof(inode_t) == INODE_SIZE, "inode size must be 128 bytes");

#pragma pack(push, 1)
typedef struct {
    uint32_t inode_no;        // 4
    uint8_t  type;            // 1
    char     name[58];        // 58
    uint8_t  checksum;        // 1 (xor of bytes 0..62)
} dirent64_t;
#pragma pack(pop)
_Static_assert(sizeof(dirent64_t) == DIRENT_SIZE, "dirent must be 64 bytes");

/* ---------- CRC32 ---------- */
static uint32_t CRC32_TAB[256];

static void crc32_init(void) {
    for (uint32_t i = 0; i < 256; ++i) {
        uint32_t c = i;
        for (int j = 0; j < 8; ++j) c = (c & 1) ? (0xEDB88320u ^ (c >> 1)) : (c >> 1);
        CRC32_TAB[i] = c;
    }
}

static uint32_t crc32(const void *data, size_t n) {
    const uint8_t *p = (const uint8_t *)data;
    uint32_t c = 0xFFFFFFFFu;
    for (size_t i = 0; i < n; ++i) c = CRC32_TAB[(c ^ p[i]) & 0xFF] ^ (c >> 8);
    return c ^ 0xFFFFFFFFu;
}

/* Finalize inode CRC: crc over first 120 bytes (128 - 8), store in lower 32 bits */
static void inode_crc_finalize(inode_t *ino) {
    uint8_t tmp[INODE_SIZE];
    memcpy(tmp, ino, INODE_SIZE);
    memset(&tmp[120], 0, 8);
    uint32_t c = crc32(tmp, 120);
    ino->inode_crc = (uint64_t)c;
}

/* Finalize directory entry checksum: XOR bytes 0..62 */
static void dirent_checksum_finalize(dirent64_t *de) {
    const uint8_t *p = (const uint8_t *)de;
    uint8_t x = 0;
    for (int i = 0; i < 63; ++i) {
        x ^= p[i];
    }
    de->checksum = x;
}

/* ---------- Helpers ---------- */
static int write_block(FILE *fp, const void *buf) {
    return fwrite(buf, BS, 1, fp) == 1 ? 0 : -1;
}

static void set_bit(uint8_t *bitmap, uint64_t idx) {
    uint64_t byte = idx / 8;
    uint8_t bit = (uint8_t)(idx % 8);
    bitmap[byte] |= (1u << bit);
}

/* ---------- Layout calculation ---------- */
static int calculate_layout(uint64_t size_kib, uint64_t inodes,
                            uint64_t *total_blocks, uint64_t *inode_table_blocks,
                            uint64_t *data_region_start, uint64_t *data_region_blocks) {
    *total_blocks = (size_kib * 1024ULL) / BS;
    *inode_table_blocks = ((inodes * INODE_SIZE) + BS - 1) / BS;
    *data_region_start = 3 + *inode_table_blocks;
    if (*data_region_start >= *total_blocks) return -1;
    *data_region_blocks = *total_blocks - *data_region_start;
    if (*data_region_blocks < 1) return -1;
    return 0;
}

/* ---------- Writers ---------- */

/* Writes superblock into block buffer and computes CRC across full block (BS-4) */
static int write_superblock(FILE *fp, uint64_t total_blocks, uint64_t inode_count,
                            uint64_t inode_table_blocks, uint64_t data_region_start,
                            uint64_t data_region_blocks, time_t now) {
    uint8_t blk[BS];
    memset(blk, 0, BS);
    superblock_t *sb = (superblock_t *)blk;
    sb->magic = MAGIC;
    sb->version = VERSION;
    sb->block_size = BS;
    sb->total_blocks = total_blocks;
    sb->inode_count = inode_count;
    sb->inode_bitmap_start = 1;
    sb->inode_bitmap_blocks = 1;
    sb->data_bitmap_start = 2;
    sb->data_bitmap_blocks = 1;
    sb->inode_table_start = 3;
    sb->inode_table_blocks = inode_table_blocks;
    sb->data_region_start = data_region_start;
    sb->data_region_blocks = data_region_blocks;
    sb->root_inode = ROOT_INO;
    sb->mtime_epoch = (uint64_t)now;
    sb->flags = 0;
    /* checksum on entire block except last 4 bytes */
    sb->checksum = 0;
    sb->checksum = crc32(blk, BS - 4);
    if (write_block(fp, blk) != 0) {
        fprintf(stderr, "write_superblock: fwrite failed: %s\n", strerror(errno));
        return -1;
    }
    return 0;
}

/* Write inode bitmap: mark inode 1 (bit 0) */
static int write_inode_bitmap(FILE *fp) {
    uint8_t blk[BS];
    memset(blk, 0, BS);
    set_bit(blk, 0); /* inode #1 => bitmap index 0 */
    if (write_block(fp, blk) != 0) {
        fprintf(stderr, "write_inode_bitmap: fwrite failed: %s\n", strerror(errno));
        return -1;
    }
    return 0;
}

/* Write data bitmap: mark first data-region block (relative index 0) */
static int write_data_bitmap(FILE *fp) {
    uint8_t blk[BS];
    memset(blk, 0, BS);
    set_bit(blk, 0); /* first block in data region => bit 0 */
    if (write_block(fp, blk) != 0) {
        fprintf(stderr, "write_data_bitmap: fwrite failed: %s\n", strerror(errno));
        return -1;
    }
    return 0;
}

/* Write inode table blocks, place root inode at index 0, others zero */
static int write_inode_table(FILE *fp, uint64_t inode_table_blocks, uint64_t data_region_start, time_t now) {
    uint32_t inodes_per_block = (uint32_t)(BS / INODE_SIZE);
    uint64_t inode_idx = 0;
    for (uint64_t b = 0; b < inode_table_blocks; ++b) {
        uint8_t blk[BS];
        memset(blk, 0, BS);
        for (uint32_t slot = 0; slot < inodes_per_block; ++slot) {
            if (inode_idx == 0) {
                inode_t *r = (inode_t *)(blk + slot * INODE_SIZE);
                memset(r, 0, INODE_SIZE);
                r->mode = (uint16_t)MODE_DIR;
                r->links = 2;
                r->uid = 0;
                r->gid = 0;
                r->size_bytes = BS; /* root dir occupies one full block */
                r->atime = (uint64_t)now;
                r->mtime = (uint64_t)now;
                r->ctime = (uint64_t)now;
                for (int i = 0; i < DIRECT_MAX; ++i) r->direct[i] = 0;
                r->direct[0] = (uint32_t)data_region_start; /* absolute block number */
                r->reserved_0 = r->reserved_1 = r->reserved_2 = 0;
                r->proj_id = GROUP_ID; /* set group/project id as requested */
                r->uid16_gid16 = 0;
                r->xattr_ptr = 0;
                inode_crc_finalize(r);
            }
            ++inode_idx;
            /* stop if we've written all inodes requested by table capacity */
            if (inode_idx >= (uint64_t)inodes_per_block * (b + 1)) {
                /* continue outer loop to write this block */
            }
        }
        if (write_block(fp, blk) != 0) {
            fprintf(stderr, "write_inode_table: fwrite failed: %s\n", strerror(errno));
            return -1;
        }
    }
    return 0;
}

/* Write data region blocks: first block contains '.' and '..' entries, rest zero */
static int write_data_region(FILE *fp, uint64_t data_region_blocks) {
    for (uint64_t i = 0; i < data_region_blocks; ++i) {
        uint8_t blk[BS];
        memset(blk, 0, BS);
        if (i == 0) {
            dirent64_t *d = (dirent64_t *)blk;
            memset(&d[0], 0, sizeof(dirent64_t));
            d[0].inode_no = ROOT_INO;
            d[0].type = 2; /* dir */
            strcpy(d[0].name, ".");
            dirent_checksum_finalize(&d[0]);

            memset(&d[1], 0, sizeof(dirent64_t));
            d[1].inode_no = ROOT_INO;
            d[1].type = 2; /* dir */
            strcpy(d[1].name, "..");
            dirent_checksum_finalize(&d[1]);
            /* rest entries are zero (inode_no = 0 => free) */
        }
        if (write_block(fp, blk) != 0) {
            fprintf(stderr, "write_data_region: fwrite failed: %s\n", strerror(errno));
            return -1;
        }
    }
    return 0;
}

/* ---------- Argument parsing & main flow ---------- */

static void usage(const char *prog) {
    fprintf(stderr, "Usage: %s --image <out.img> --size-kib <180..4096> --inodes <128..512>\n", prog);
}

static int parse_uint64_str(const char *s, uint64_t *out) {
    char *end = NULL;
    errno = 0;
    unsigned long long v = strtoull(s, &end, 10);
    if (errno != 0 || *end != '\0') return -1;
    *out = (uint64_t)v;
    return 0;
}

int main(int argc, char *argv[]) {
    crc32_init();

    if (argc < 7) {
        usage(argv[0]);
        return 1;
    }

    const char *image_name = NULL;
    uint64_t size_kib = 0;
    uint64_t inodes = 0;

    for (int i = 1; i < argc; ++i) {
        if (strcmp(argv[i], "--image") == 0 && i + 1 < argc) {
            image_name = argv[++i];
        } else if (strcmp(argv[i], "--size-kib") == 0 && i + 1 < argc) {
            if (parse_uint64_str(argv[++i], &size_kib) != 0) {
                fprintf(stderr, "Invalid --size-kib value\n");
                return 1;
            }
        } else if (strcmp(argv[i], "--inodes") == 0 && i + 1 < argc) {
            if (parse_uint64_str(argv[++i], &inodes) != 0) {
                fprintf(stderr, "Invalid --inodes value\n");
                return 1;
            }
        } else {
            fprintf(stderr, "Unknown/invalid argument: %s\n", argv[i]);
            usage(argv[0]);
            return 1;
        }
    }

    if (!image_name) {
        fprintf(stderr, "Missing --image\n");
        return 1;
    }
    if (size_kib < MIN_SIZE_KIB || size_kib > MAX_SIZE_KIB || (size_kib % 4) != 0) {
        fprintf(stderr, "size-kib must be %u..%u and multiple of 4\n", MIN_SIZE_KIB, MAX_SIZE_KIB);
        return 1;
    }
    if (inodes < MIN_INODES || inodes > MAX_INODES) {
        fprintf(stderr, "inodes must be %u..%u\n", MIN_INODES, MAX_INODES);
        return 1;
    }

    uint64_t total_blocks, inode_table_blocks, data_region_start, data_region_blocks;
    if (calculate_layout(size_kib, inodes, &total_blocks, &inode_table_blocks, &data_region_start, &data_region_blocks) != 0) {
        fprintf(stderr, "Error: insufficient space for filesystem layout\n");
        return 1;
    }

    FILE *fp = fopen(image_name, "wb");
    if (!fp) {
        fprintf(stderr, "Error: cannot create image '%s': %s\n", image_name, strerror(errno));
        return 1;
    }

    time_t now = time(NULL);
    if (now == (time_t)-1) now = 0;

    /* Write blocks in order */
    if (write_superblock(fp, total_blocks, inodes, inode_table_blocks, data_region_start, data_region_blocks, now) != 0) goto fail;
    if (write_inode_bitmap(fp) != 0) goto fail;
    if (write_data_bitmap(fp) != 0) goto fail;
    if (write_inode_table(fp, inode_table_blocks, data_region_start, now) != 0) goto fail;
    if (write_data_region(fp, data_region_blocks) != 0) goto fail;

    /* verify size */
    if (fflush(fp) != 0) {
        fprintf(stderr, "fflush failed: %s\n", strerror(errno));
        goto fail;
    }
    long cur = ftell(fp);
    if (cur < 0) {
        fprintf(stderr, "ftell failed: %s\n", strerror(errno));
        goto fail;
    }
    long long expected = (long long)total_blocks * (long long)BS;
    if ((long long)cur != expected) {
        fprintf(stderr, "Error: output size mismatch (expected %" PRId64 ", got %ld)\n", (int64_t)expected, cur);
        goto fail;
    }

    if (fclose(fp) != 0) {
        fprintf(stderr, "fclose failed: %s\n", strerror(errno));
        return 1;
    }

    printf("Created image '%s' (%" PRIu64 " KiB) with %" PRIu64 " inodes\n", image_name, size_kib, inodes);
    return 0;

fail:
    fclose(fp);
    unlink(image_name);
    return 1;
}
