#include <stdio.h>
#include <string.h>
#include <stdlib.h>

static int v = 0, nostdlib = 0, strip_all = 0, impure = 0;
static unsigned long output_size, text_size = 0, data_size = 0, bss_size = 0;
static void *output = NULL, *text = NULL, *data = NULL;
static unsigned long text_ptr = 0, data_ptr = 0, bss_ptr = 0;

#define MAX_OBJECTS 256

struct object {
    char *filename;
    void *raw;
    long size;
    struct exec *header;
    struct relocation_info *trelocs, *drelocs;
    struct nlist *symtab;
    char *strtab;
    int symtab_count, trelocs_count, drelocs_count;
    unsigned long text_slide, data_slide, bss_slide;
};

struct object objects[MAX_OBJECTS];
int object_count = 0;

#define DIV_ROUNDUP(a, b) (((a) + ((b) - 1)) / (b))
#define ALIGN_UP(x, a) (DIV_ROUNDUP((x), (a)) * (a))

#define PAGE_SIZE 4096

struct exec {
    unsigned int a_midmag;
    unsigned int a_text;
    unsigned int a_data;
    unsigned int a_bss;
    unsigned int a_syms;
    unsigned int a_entry;
    unsigned int a_trsize;
    unsigned int a_drsize;
};

struct nlist {
    int n_strx;
    unsigned char n_type;
    char n_other;
    short n_desc;
    unsigned int n_value;
};

struct relocation_info {
    int r_address;
    unsigned int r_type;
};

#define N_GETMAGIC(exec) ((exec).a_midmag & 0xffff)

#define OMAGIC 0407

#define N_UNDF 0
#define N_ABS 2
#define N_TEXT 4
#define N_DATA 6
#define N_BSS 8
#define N_FN 15
#define N_EXT 1
#define N_TYPE 036

void apply_slides(struct object *object) {
    int i;
    for (i = 0; i < object->symtab_count; i++) {
        struct nlist *symbol = &object->symtab[i];
        unsigned long final_slide = 0;

        if (symbol->n_type != N_TEXT
         && symbol->n_type != N_DATA
         && symbol->n_type != N_BSS) {
            continue;
        }

        switch (symbol->n_type) {
            case N_BSS:
                final_slide += text_size;
                final_slide += data_size;
                final_slide += object->bss_slide;
                break;
            case N_DATA:
                final_slide += text_size;
                final_slide += object->data_slide;
                break;
            case N_TEXT:
                final_slide += object->text_slide;
                break;
        }

        symbol->n_value += final_slide;
    }
    for (i = 0; i < object->trelocs_count; i++) {
        struct relocation_info *rel = &object->trelocs[i];

        rel->r_address += object->text_slide;
    }
    for (i = 0; i < object->drelocs_count; i++) {
        struct relocation_info *rel = &object->drelocs[i];

        rel->r_address += text_size + object->data_slide;
    }
}

void paste(struct object *object) {
    struct exec *header;
    char *obj_text, *obj_data;
    unsigned long obj_text_size, obj_data_size, obj_bss_size;

    header = object->header;

    object->text_slide = text_ptr;
    obj_text = (char *)object->raw + sizeof(struct exec);
    if (impure) {
        obj_text_size = header->a_text;
    } else {
        obj_text_size = ALIGN_UP(header->a_text, PAGE_SIZE);
    }

    memcpy(text, obj_text, obj_text_size);

    text_ptr += obj_text_size;

    object->data_slide = data_ptr;
    obj_data = (char *)object->raw + sizeof(struct exec) + header->a_text;
    if (impure) {
        obj_data_size = header->a_data;
    } else {
        obj_data_size = ALIGN_UP(header->a_data, PAGE_SIZE);
    }

    memcpy(text, obj_data, obj_data_size);

    data_ptr += obj_data_size;

    object->bss_slide = bss_ptr;
    if (impure) {
        obj_bss_size = header->a_bss;
    } else {
        obj_bss_size = ALIGN_UP(header->a_bss, PAGE_SIZE);
    }
    bss_ptr += obj_bss_size;
}

void strip_arg(int *argc, char *argv[], int index) {
    int i;

    for (i = index; i < *argc; i++) {
        argv[i] = argv[i + 1];
    }

    *argc -= 1;
}

int initialise_gen(void *object, long object_size, char *filename, int quiet) {
    int err = 0;
    struct exec *header;
    struct nlist *symtab;
    struct relocation_info *trelocs, *drelocs;
    char *strtab;
    int symtab_count, trelocs_count, drelocs_count;
    unsigned int symtab_off, strtab_off, trelocs_off, drelocs_off;
    struct object *new_object;

    header = object;

    if (N_GETMAGIC(*header) != OMAGIC) {
        if (!quiet) {
            fprintf(stderr, "pdld: error: %s is not a valid a.out object file.\n", filename);
        }
        err = 1;
        goto out;
    }

    if (impure) {
        text_size += header->a_text;
        data_size += header->a_data;
        bss_size += header->a_bss;
    } else {
        text_size += ALIGN_UP(header->a_text, PAGE_SIZE);
        data_size += ALIGN_UP(header->a_data, PAGE_SIZE);
        bss_size += ALIGN_UP(header->a_bss, PAGE_SIZE);
    }

    trelocs_off = sizeof(struct exec) + header->a_text + header->a_data;
    drelocs_off = trelocs_off + header->a_trsize;
    symtab_off = drelocs_off + header->a_drsize;
    strtab_off = symtab_off + header->a_syms;

    trelocs_count = header->a_trsize / sizeof(struct relocation_info);
    drelocs_count = header->a_drsize / sizeof(struct relocation_info);
    symtab_count = header->a_syms / sizeof(struct nlist);

    symtab = (void *)((char *)object + symtab_off);
    trelocs = (void *)((char *)object + trelocs_off);
    drelocs = (void *)((char *)object + drelocs_off);
    strtab = (char *)object + strtab_off;

    if (object_count == MAX_OBJECTS) {
        fprintf(stderr, "pdld: error: Too many objects\n");
        err = 1;
        goto out;
    }
    new_object = &objects[object_count];
    object_count++;

    new_object->filename = filename;
    new_object->raw = object;
    new_object->size = object_size;
    new_object->header = header;
    new_object->trelocs = trelocs;
    new_object->drelocs = drelocs;
    new_object->symtab = symtab;
    new_object->strtab = strtab;
    new_object->trelocs_count = trelocs_count;
    new_object->drelocs_count = drelocs_count;
    new_object->symtab_count = symtab_count;

out:
    return err;
}

struct ar_header {
    char name[16];
    char mtime[12];
    char owner[6];
    char group[6];
    char mode[8];
    char size[10];
    char endsig[2];
};

unsigned long conv_dec(char *str, int max) {
    unsigned long value = 0;
    while (*str != ' ' && max-- > 0) {
        value *= 10;
        value += *str++ - '0';
    }
    return value;
}

int initialise_archive(FILE *ar_file) {
    int err = 0;
    void *object = NULL;

    if (fseek(ar_file, 8, SEEK_SET) != 0) {
        goto out_perror;
    }

    for (;;) {
        struct ar_header header;
        unsigned long size, size_aligned;

        if (fread(&header, sizeof(struct ar_header), 1, ar_file) != 1) {
            if (feof(ar_file) == 1) {
                break;
            }
            goto out_perror;
        }

        size = conv_dec(header.size, 10);
        size_aligned = size % 2 ? size + 1 : size;

        if (v) {
            fprintf(stderr, "Archiver: Processing file %.16s (size %lu)\n", header.name, size);
        }

        object = malloc(size_aligned);
        if (object == NULL) {
            goto out_perror;
        }

        if (fread(object, size_aligned, 1, ar_file) != 1) {
            goto out_perror;
        }

        if (initialise_gen(object, size, ""/*name*/, 1) != 0) {
            free(object);
        }

        object = NULL;
    }

    goto out;

out_perror:
    err = 1;
    perror("pdld: error");

out:
    if (object != NULL && err != 0) {
        free(object);
    }
    return err;
}

int initialise_object(char *filename) {
    int err = 0;
    FILE *object_file = NULL;
    long object_size;
    void *object = NULL;
    char ar_magic[8];

    object_file = fopen(filename, "r");
    if (object_file == NULL) {
        goto out_perror;
    }

    if (fread(ar_magic, 8, 1, object_file) != 1) {
        goto out_perror;
    }

    if (memcmp(ar_magic, "!<arch>\n", 8) == 0) {
        if (v) {
            fprintf(stderr, "File %s is an archive\n", filename);
        }
        err = initialise_archive(object_file);
        goto out;
    }

    if (fseek(object_file, 0, SEEK_END) != 0) {
        goto out_perror;
    }

    object_size = ftell(object_file);
    if (object_size == -1) {
        goto out_perror;
    }

    rewind(object_file);

    if (v) {
        fprintf(stderr, "Object file is %ld bytes long.\n", object_size);
    }

    object = malloc(object_size);
    if (object == NULL) {
        goto out_perror;
    }

    if (fread(object, object_size, 1, object_file) != 1) {
        goto out_perror;
    }

    err = initialise_gen(object, object_size, filename, 0);

    goto out;

out_perror:
    err = 1;
    perror("pdld: error");

out:
    if (object_file != NULL) {
        fclose(object_file);
    }
    if (object != NULL && err != 0) {
        free(object);
    }
    return err;
}

int get_symbol(struct object **obj_out, int *index, char *name) {
    int object_i, symbol_i;

    for (object_i = 0; object_i < object_count; object_i++) {
        struct object *object = &objects[object_i];
        for (symbol_i = 0; symbol_i < object->symtab_count; symbol_i++) {
            struct nlist *sym = &object->symtab[symbol_i];

            char *symname = object->strtab + sym->n_strx;

            if (strcmp(symname, name) == 0) {
                *obj_out = object;
                *index = symbol_i;
                return 0;
            }
        }
    }

    fprintf(stderr, "pdld: error: Undefined symbol: %s\n", name);
    return 1;
}

int glue(struct object *object) {
    int err = 0, i;

    for (i = 0; i < object->trelocs_count; i++) {
        struct relocation_info *r = &object->trelocs[i];
        struct nlist *symbol;
        long result;

        int symbolnum = r->r_type & 0xffffff;
        int pcrel = (r->r_type & (1 << 24)) >> 24;
        int ext = (r->r_type & (1 << 27)) >> 27;
        int baserel = (r->r_type & (1 << 28)) >> 28;
        int jmptable = (r->r_type & (1 << 29)) >> 29;
        int rel = (r->r_type & (1 << 30)) >> 30;
        int copy = (r->r_type & (1 << 31)) >> 31;

        int length = (r->r_type & (3 << 25)) >> 25;
        switch (length) {
            case 0: length = 1; break;
            case 1: length = 2; break;
            case 2: length = 4; break;
        }

        if (baserel || jmptable || rel || copy) {
            fprintf(stderr, "pdld: Unsupported relocation type\n");
            err = 1;
            goto out;
        }

        if (ext) {
            struct object *symobj;
            int symindex;
            char *symname;

            symname = object->strtab + object->symtab[symbolnum].n_strx;

            err = get_symbol(&symobj, &symindex, symname);
            if (err != 0) {
                err = 1;
                goto out;
            }

            symbol = &symobj->symtab[symindex];
        } else {
            symbol = &object->symtab[symbolnum];
        }

        if (pcrel) {
            result = (long)symbol->n_value - (long)r->r_address;
        } else {
            result = symbol->n_value;
        }

        memcpy((char *)output + r->r_address, &result, length);
    }

out:
    return err;
}

int main(int argc, char *argv[]) {
    int err = 0, i;
    struct exec *header;
    struct object *entry_obj;
    int entry_index;
    FILE *output_file = NULL;
    char *output_filename = "a.out";

    /* Find the verbose flag before everything else */
    for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--verbose") == 0) {
            fprintf(stderr, "PDLD: Public Domain a.out Linker\n\n");
            fprintf(stderr, "Being verbose.\n");
            v = 1;
            strip_arg(&argc, argv, i);
            break;
        }
    }

    for (i = 1; i < argc; ) {
        if (strcmp(argv[i], "-nostdlib") == 0) {
            nostdlib = 1;
            if (v) {
                fprintf(stderr, "Without standard library.\n");
            }
        } else if (strcmp(argv[i], "-s") == 0) {
            strip_all = 1;
            if (v) {
                fprintf(stderr, "Strip all.\n");
            }
        } else if (strcmp(argv[i], "-N") == 0) {
            impure = 1;
            if (v) {
                fprintf(stderr, "Make impure.\n");
            }
        } else if (strcmp(argv[i], "-o") == 0) {
            if (i + 1 == argc) {
                fprintf(stderr, "pdld: error: Output flag passed without output file name.\n");
                err = 1;
                goto out;
            }
            output_filename = argv[i + 1];
            if (v) {
                fprintf(stderr, "Output filename: %s\n", output_filename);
            }
            strip_arg(&argc, argv, i + 1);
        } else {
            if (*argv[i] != '-') {
                i++;
                continue;
            }
            fprintf(stderr, "pdld: warning: Unrecognised option: %s\n", argv[i]);
        }

        strip_arg(&argc, argv, i);
    }

    for (i = 1; i < argc; i++) {
        if (v) {
            fprintf(stderr, "Initialising object: %s\n", argv[i]);
        }

        if (initialise_object(argv[i]) != 0) {
            err = 1;
            goto out;
        }
    }

    if (v) {
        fprintf(stderr, "Calculated text size: %lu\n", text_size);
        fprintf(stderr, "Calculated data size: %lu\n", data_size);
        fprintf(stderr, "Calculated bss size: %lu\n", bss_size);
    }

    if (impure) {
        output_size = sizeof(struct exec) + text_size + data_size;
    } else {
        output_size = ALIGN_UP(sizeof(struct exec), PAGE_SIZE) + text_size + data_size;
    }

    output = malloc(output_size);
    if (output == NULL) {
        goto out_perror;
    }

    memset(output, 0, output_size);

    header = output;

    if (impure) {
        text = (void *)((char *)output + sizeof(struct exec));
    } else {
        text = (void *)((char *)output + ALIGN_UP(sizeof(struct exec), PAGE_SIZE));
    }

    data = (void *)((char *)text + text_size);

    for (i = 0; i < object_count; i++) {
        paste(&objects[i]);
    }

    for (i = 0; i < object_count; i++) {
        apply_slides(&objects[i]);
    }

    for (i = 0; i < object_count; i++) {
        if (glue(&objects[i]) != 0) {
            err = 1;
            goto out;
        }
    }

    if (get_symbol(&entry_obj, &entry_index, "___start") == 1) {
        fprintf(stderr, "pdld: error: Cannot find entry point\n");
        err = 1;
        goto out;
    }

    header->a_midmag = OMAGIC;
    header->a_text = text_size;
    header->a_data = data_size;
    header->a_bss = bss_size;
    header->a_entry = entry_obj->symtab[entry_index].n_value;

    output_file = fopen(output_filename, "w");
    if (output_file == NULL) {
        goto out_perror;
    }

    if (fwrite(output, output_size, 1, output_file) != 1) {
        goto out_perror;
    }

    goto out;

out_perror:
    err = 1;
    perror("pdld: error");

out:
    for (i = 0; i < object_count; i++) {
        free(objects[i].raw);
    }
    if (output != NULL) {
        free(output);
    }
    if (output_file != NULL) {
        fclose(output_file);
    }
    return err;
}
