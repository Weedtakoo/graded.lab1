// Ziya Pirizade 251ADB128
// https://github.com/Weedtakoo/graded.lab1
// Compile with: gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
// Resources used: Ortus materials; ChatGPT.
// ChatGPT conversation history: <https://chatgpt.com/share/6adf2384-331c-83eb-a0c1-774e52a2506c>

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#define FIRST "ziya"
#define LAST "pirizade"
#define STUDENT_ID "251ADB128"

// The basic types are from "2- Introduction to C.pptx"; the struct examples are in
// "6-Advanced pointers, dynamic memory, structures, preprocessor directives.pptx".
typedef enum { END, NUMBER, PLUS, MINUS, TIMES, DIVIDE, POWER, LEFT, RIGHT, INVALID } TokenType;
typedef struct { long long i; double f; int floating; } Value;
typedef struct { TokenType type; Value value; size_t pos; } Token;
typedef struct {
    const unsigned char *text;
    size_t length, index, start, endpos, error_pos;
    Token token;
    int error;
} Parser;

/* The first error is kept because later parser calls could find other errors.
   The original error is the one that should be reported. */
static void set_error(Parser *p, size_t pos)
{
    if (!p->error) {
        p->error = 1;
        p->error_pos = pos;
    }
}

/* Token positions start at 1 on each line. The END token points just after
   the last character, so a missing operand can be reported at the newline
   or at the end of the file.
   Reference: "4- Arrays, Strings, Pointers.pptx". */
static void next_token(Parser *p)
{
    Token t = {0};
    while (p->index < p->length && isspace(p->text[p->index])) p->index++;
    if (p->index == p->length) {
        t.type = END;
        t.pos = p->index + 1;
        p->token = t;
        return;
    }

    size_t first = p->index;
    unsigned char ch = p->text[p->index];
    t.pos = first + 1;

    if (ch >= '0' && ch <= '9') {
        long long number = 0;
        double decimal = 0.0, place = 0.1;
        int overflow = 0, has_dot = 0;

        while (p->index < p->length && p->text[p->index] >= '0' && p->text[p->index] <= '9') {
            int digit = p->text[p->index] - '0';
            if (!overflow) {
                if (number > (LLONG_MAX - digit) / 10) overflow = 1;
                else number = number * 10 + digit;
            }
            decimal = decimal * 10.0 + digit;
            p->index++;
        }

        if (p->index < p->length && p->text[p->index] == '.') {
            if (p->index + 1 >= p->length || p->text[p->index + 1] < '0' || p->text[p->index + 1] > '9') {
                t.type = INVALID;
                t.pos = p->index + 1;
                p->token = t;
                return;
            }
            has_dot = 1;
            p->index++;
            while (p->index < p->length && p->text[p->index] >= '0' && p->text[p->index] <= '9') {
                decimal += (p->text[p->index++] - '0') * place;
                place *= 0.1;
            }
        }

        if ((overflow && !has_dot) || (has_dot && !isfinite(decimal))) t.type = INVALID;
        else {
            t.type = NUMBER;
            t.value.i = number;
            t.value.f = has_dot ? decimal : (double)number;
            t.value.floating = has_dot;
        }
        p->token = t;
        return;
    }

    p->index++;
    switch (ch) {
        case '+': t.type = PLUS; break;
        case '-': t.type = MINUS; break;
        case '/': t.type = DIVIDE; break;
        case '(': t.type = LEFT; break;
        case ')': t.type = RIGHT; break;
        case '*':
            if (p->index < p->length && p->text[p->index] == '*') {
                p->index++;
                t.type = POWER;
            } else t.type = TIMES;
            break;
        default: t.type = INVALID; break;
    }
    p->token = t;
}

/* Integer operations use long long when both operands are integers. If either
   operand is a float, both operands are converted to double.
   Reference: "2- Introduction to C.pptx". */
static int add_int(long long a, long long b, long long *out)
{
    *out = a + b;
    return 1;
}

static int sub_int(long long a, long long b, long long *out)
{
    *out = a - b;
    return 1;
}

static int mul_int(long long a, long long b, long long *out)
{
    *out = a * b;
    return 1;
}

/* Exponentiation by squaring reduces the number of multiplications needed
   compared with multiplying the base repeatedly. */
static int int_power(long long base, long long exponent, long long *out)
{
    long long result = 1;
    while (exponent > 0) {
        if (exponent % 2 && !mul_int(result, base, &result)) return 0;
        exponent /= 2;
        if (exponent && !mul_int(base, base, &base)) return 0;
    }
    *out = result;
    return 1;
}

static double as_double(Value v) { return v.floating ? v.f : (double)v.i; }
static Value int_value(long long n) { Value v = {n, (double)n, 0}; return v; }
static Value float_value(double n) { Value v = {0, n, 1}; return v; }

/* Each function handles a different operator level. This gives ** higher
   precedence than * and /, and gives * and / higher precedence than + and -.
   Reference: "3- Control flow and functions.pptx". */
static Value expression(Parser *p);
static Value term(Parser *p);
static Value power(Parser *p);
static Value primary(Parser *p);

static Value calculate(Parser *p, TokenType op, Value a, Value b, size_t op_pos, size_t rhs_pos)
{
    long long n;
    double x, y, result;

    /* Division by zero is reported at the start of the right operand. */
    if (op == DIVIDE && as_double(b) == 0.0) {
        set_error(p, rhs_pos);
        return int_value(0);
    }

    if (!a.floating && !b.floating) {
        if (op == PLUS && add_int(a.i, b.i, &n)) return int_value(n);
        if (op == MINUS && sub_int(a.i, b.i, &n)) return int_value(n);
        if (op == TIMES && mul_int(a.i, b.i, &n)) return int_value(n);
        if (op == DIVIDE && !(a.i == LLONG_MIN && b.i == -1)) return int_value(a.i / b.i);

        set_error(p, op_pos);
        return int_value(0);
    }

    x = as_double(a);
    y = as_double(b);
    if (op == PLUS) result = x + y;
    else if (op == MINUS) result = x - y;
    else if (op == TIMES) result = x * y;
    else result = x / y;

    /* A non-finite floating-point result is reported at the operator. */
    if (!isfinite(result)) {
        set_error(p, op_pos);
        return int_value(0);
    }
    return float_value(result);
}

/* A primary value is a number or an expression inside parentheses. If parsing
   cannot continue, the current token position identifies where the expected
   operand or closing parenthesis is missing. */
static Value primary(Parser *p)
{
    Value v = int_value(0);
    if (p->error) return v;

    if (p->token.type == NUMBER) {
        v = p->token.value;
        next_token(p);
        return v;
    }
    if (p->token.type == LEFT) {
        next_token(p);
        v = expression(p);
        if (p->error) return v;
        if (p->token.type != RIGHT) {
            set_error(p, p->token.pos);
            return v;
        }
        next_token(p);
        return v;
    }
    set_error(p, p->token.pos);
    return v;
}

/* ChatGPT helped me fix the right-associative exponentiation test. I learned
   that calling power() recursively for the exponent makes 2 ** 3 ** 2 evaluate
   as 2 ** (3 ** 2), producing 512. */
static Value power(Parser *p)
{
    Value a = primary(p);
    while (!p->error && p->token.type == POWER) {
        size_t op_pos = p->token.pos;
        next_token(p);
        size_t rhs_pos = p->token.pos;
        Value b = power(p);
        if (p->error) return a;

        double exponent = as_double(b);
        if (!a.floating && !b.floating && exponent < 0.0) {
            set_error(p, rhs_pos);
            return a;
        }

        if (!a.floating && !b.floating) {
            long long n;
            if (!int_power(a.i, b.i, &n)) {
                set_error(p, op_pos);
                return a;
            }
            a = int_value(n);
        } else {
            double result = pow(as_double(a), exponent);
            if (!isfinite(result)) {
                set_error(p, op_pos);
                return a;
            }
            a = float_value(result);
        }
    }
    return a;
}

/* Multiplication and division are handled after powers and evaluated from
   left to right. */
static Value term(Parser *p)
{
    Value a = power(p);
    while (!p->error && (p->token.type == TIMES || p->token.type == DIVIDE)) {
        TokenType op = p->token.type;
        size_t op_pos = p->token.pos;
        next_token(p);
        size_t rhs_pos = p->token.pos;
        Value b = power(p);
        if (p->error) return a;
        a = calculate(p, op, a, b, op_pos, rhs_pos);
    }
    return a;
}

/* Addition and subtraction are handled after the higher-precedence operators
   and evaluated from left to right. */
static Value expression(Parser *p)
{
    Value a = term(p);
    while (!p->error && (p->token.type == PLUS || p->token.type == MINUS)) {
        TokenType op = p->token.type;
        size_t op_pos = p->token.pos;
        next_token(p);
        size_t rhs_pos = p->token.pos;
        Value b = term(p);
        if (p->error) return a;
        a = calculate(p, op, a, b, op_pos, rhs_pos);
    }
    return a;
}

/* Blank lines and lines whose first non-whitespace character is # are ignored.
   A # elsewhere is left for the tokenizer to reject. */
static int blank_or_comment(const unsigned char *s, size_t n)
{
    size_t i = 0;
    while (i < n && isspace(s[i])) i++;
    return i == n || s[i] == '#';
}

/* The file is read into one buffer so the parser can scan it directly. This
   avoids repeatedly copying the input and helps with large files.
   Reference: "5-Files, Arguments, Directories.pptx". */
static int read_file(FILE *file, unsigned char **text, size_t *length)
{
    if (fseek(file, 0, SEEK_END) != 0) return 0;
    long size = ftell(file);
    if (size < 0 || fseek(file, 0, SEEK_SET) != 0) return 0;
    *length = (size_t)size;
    *text = malloc(*length + 1);
    if (!*text) return 0;
    if (fread(*text, 1, *length, file) != *length) {
        free(*text);
        *text = NULL;
        return 0;
    }
    (*text)[*length] = '\0';
    return 1;
}

/* Each nonblank, non-comment line is evaluated separately. Results are saved
   temporarily until the whole file is checked, allowing an error to replace
   earlier results with the required error message.
   Reference: "3- Control flow and functions.pptx". */
static int evaluate_file(FILE *input, FILE *results, size_t *error_pos)
{
    unsigned char *text = NULL;
    size_t length = 0, line = 0;
    if (!read_file(input, &text, &length)) {
        fprintf(stderr, "calc: cannot read input file\n");
        return -1;
    }

    while (line < length) {
        size_t end = line;
        while (end < length && text[end] != '\n') end++;
        size_t line_len = end - line;
        if (!blank_or_comment(text + line, line_len)) {
            Parser p = {0};
            p.text = text + line;
            p.length = line_len;
            p.start = 1;
            p.endpos = line_len + 1;
            next_token(&p);
            Value v = expression(&p);
            if (!p.error && p.token.type != END) set_error(&p, p.token.pos);
            if (p.error) {
                /* ChatGPT helped me fix incorrect error positions on later
                   lines. The parser's position is local to the current line,
                   so the line offset must be added to get the correct position
                   in the complete file. */
                *error_pos = line + p.error_pos;
                free(text);
                return 1;
            }
            if ((v.floating ? fprintf(results, "%.15g\n", v.f) : fprintf(results, "%lld\n", v.i)) < 0) {
                fprintf(stderr, "calc: cannot write temporary results\n");
                free(text);
                return -1;
            }
        }
        line = end < length ? end + 1 : length;
    }

    free(text);
    return 0;
}

/* String operations and dynamic allocation are covered in
   "4- Arrays, Strings, Pointers.pptx" and
   "6-Advanced pointers, dynamic memory, structures, preprocessor directives.pptx". */
static char *copy_string(const char *s)
{
    size_t n = strlen(s);
    char *p = malloc(n + 1);
    if (p) memcpy(p, s, n + 1);
    return p;
}

static char *join_path(const char *dir, const char *name)
{
    size_t a = strlen(dir), b = strlen(name);
    int slash = a > 0 && dir[a - 1] != '/';
    char *path = malloc(a + b + (size_t)slash + 1);
    if (!path) return NULL;
    memcpy(path, dir, a);
    if (slash) path[a++] = '/';
    memcpy(path + a, name, b + 1);
    return path;
}

static const char *base_name(const char *path)
{
    const char *p = strrchr(path, '/');
    return p ? p + 1 : path;
}

static char *file_stem(const char *path)
{
    const char *name = base_name(path);
    size_t n = strlen(name);
    if (n >= 4 && strcmp(name + n - 4, ".txt") == 0) n -= 4;
    char *stem = malloc(n + 1);
    if (stem) { memcpy(stem, name, n); stem[n] = '\0'; }
    return stem;
}

static char *folder_name(const char *path)
{
    size_t n = strlen(path);
    while (n > 1 && path[n - 1] == '/') n--;
    size_t start = n;
    while (start > 0 && path[start - 1] != '/') start--;
    if (start == n) return copy_string("/");
    char *name = malloc(n - start + 1);
    if (name) { memcpy(name, path + start, n - start); name[n - start] = '\0'; }
    return name;
}

static char *output_name(const char *input)
{
    char *stem = file_stem(input);
    if (!stem) return NULL;
    size_t n = strlen(stem) + strlen(FIRST) + strlen(LAST) + strlen(STUDENT_ID) + 8;
    char *name = malloc(n);
    if (name) snprintf(name, n, "%s_%s_%s_%s.txt", stem, FIRST, LAST, STUDENT_ID);
    free(stem);
    return name;
}

static char *default_output_dir(const char *base)
{
    size_t n = strlen(base) + strlen(FIRST) + strlen(STUDENT_ID) + 3;
    char *name = malloc(n);
    if (name) snprintf(name, n, "%s_%s_%s", base, FIRST, STUDENT_ID);
    return name;
}

static int make_directory(const char *path)
{
    struct stat info;
    if (stat(path, &info) == 0) {
        if (S_ISDIR(info.st_mode)) return 0;
        fprintf(stderr, "calc: output path is not a directory: %s\n", path);
        return -1;
    }
    if (errno != ENOENT || mkdir(path, 0777) != 0) {
        fprintf(stderr, "calc: cannot create directory %s: %s\n", path, strerror(errno));
        return -1;
    }
    return 0;
}

/* Results are copied in fixed-size chunks instead of loading all results into
   another memory buffer. */
static int copy_results(FILE *from, FILE *to)
{
    char buf[8192];
    size_t n;
    rewind(from);
    while ((n = fread(buf, 1, sizeof(buf), from)) > 0)
        if (fwrite(buf, 1, n, to) != n) return -1;
    return ferror(from) ? -1 : 0;
}

static int process_file(const char *input_path, const char *output_dir)
{
    FILE *input = fopen(input_path, "rb"), *results = NULL, *output = NULL;
    char *name = NULL, *path = NULL;
    size_t error_pos = 0;
    int status, rc = -1;

    if (!input) {
        fprintf(stderr, "calc: cannot open %s: %s\n", input_path, strerror(errno));
        return -1;
    }
    results = tmpfile();
    if (!results) { fprintf(stderr, "calc: cannot create temporary file\n"); goto done; }
    status = evaluate_file(input, results, &error_pos);
    if (status < 0) goto done;

    name = output_name(input_path);
    if (!name || !(path = join_path(output_dir, name))) {
        fprintf(stderr, "calc: not enough memory for output path\n");
        goto done;
    }
    output = fopen(path, "wb");
    if (!output) { fprintf(stderr, "calc: cannot write %s: %s\n", path, strerror(errno)); goto done; }

    /* ChatGPT helped me fix the case where earlier results were still written
       after a later expression failed. The output must contain only ERROR:<pos>
       when any expression in the file has an error. */
    if (status == 1) {
        if (fprintf(output, "ERROR:%zu\n", error_pos) < 0) {
            fprintf(stderr, "calc: failed writing output file %s\n", path);
            goto done;
        }
    } else if (copy_results(results, output) != 0) {
        fprintf(stderr, "calc: failed writing output file %s\n", path);
        goto done;
    }

    if (fclose(output) != 0) {
        output = NULL;
        fprintf(stderr, "calc: failed closing output file %s\n", path);
        goto done;
    }
    output = NULL;
    rc = 0;
done:
    if (output) fclose(output);
    if (results) fclose(results);
    fclose(input);
    free(name);
    free(path);
    return rc;
}

static int is_txt(const char *name)
{
    size_t n = strlen(name);
    return n >= 4 && strcmp(name + n - 4, ".txt") == 0;
}

static int compare_names(const void *a, const void *b)
{
    return strcmp(*(char *const *)a, *(char *const *)b);
}

/* Only regular .txt files directly inside the directory are processed.
   Names are collected and sorted before processing.
   Reference: "5-Files, Arguments, Directories.pptx". */
static int process_directory(const char *input_dir, const char *output_dir)
{
    DIR *dir = opendir(input_dir);
    if (!dir) { fprintf(stderr, "calc: cannot open directory %s: %s\n", input_dir, strerror(errno)); return -1; }

    char **names = NULL;
    size_t count = 0, cap = 0;
    struct dirent *entry;
    int rc = 0;

    while ((entry = readdir(dir)) != NULL) {
        if (!is_txt(entry->d_name)) continue;
        char *full = join_path(input_dir, entry->d_name);
        struct stat info;
        if (!full) { rc = -1; break; }
        int regular = stat(full, &info) == 0 && S_ISREG(info.st_mode);
        free(full);
        if (!regular) continue;

        if (count == cap) {
            size_t next_cap = cap ? cap * 2 : 16;
            if (next_cap < cap || next_cap > (size_t)-1 / sizeof(*names)) { rc = -1; break; }
            char **new_names = realloc(names, next_cap * sizeof(*names));
            if (!new_names) { rc = -1; break; }
            names = new_names;
            cap = next_cap;
        }
        names[count] = copy_string(entry->d_name);
        if (!names[count]) { rc = -1; break; }
        count++;
    }
    closedir(dir);

    if (rc == 0) {
        if (count > 1) qsort(names, count, sizeof(*names), compare_names);
        for (size_t i = 0; i < count; i++) {
            char *path = join_path(input_dir, names[i]);
            if (!path || process_file(path, output_dir) != 0) rc = -1;
            free(path);
            if (rc != 0) break;
        }
    }

    for (size_t i = 0; i < count; i++) free(names[i]);
    free(names);
    if (rc) fprintf(stderr, "calc: directory processing failed\n");
    return rc;
}

static void usage(void)
{
    fprintf(stderr, "Usage: calc [-d DIR | --dir DIR] [-o OUTDIR | --output-dir OUTDIR] [input.txt]\n");
}

int main(int argc, char **argv)
{
    const char *input_file = NULL, *input_dir = NULL, *chosen_output = NULL;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-d") == 0 || strcmp(argv[i], "--dir") == 0) {
            if (input_dir || input_file || i + 1 >= argc) { usage(); return 2; }
            input_dir = argv[++i];
        } else if (strcmp(argv[i], "-o") == 0 || strcmp(argv[i], "--output-dir") == 0) {
            if (chosen_output || i + 1 >= argc) { usage(); return 2; }
            chosen_output = argv[++i];
        } else if (argv[i][0] == '-') {
            fprintf(stderr, "calc: unknown option: %s\n", argv[i]);
            usage();
            return 2;
        } else {
            if (input_file || input_dir) { usage(); return 2; }
            input_file = argv[i];
        }
    }

    if ((!input_file && !input_dir) || (input_file && input_dir)) { usage(); return 2; }

    char *base = input_dir ? folder_name(input_dir) : file_stem(input_file);
    char *output_dir = chosen_output ? copy_string(chosen_output) : (base ? default_output_dir(base) : NULL);
    free(base);
    if (!output_dir) { fprintf(stderr, "calc: not enough memory\n"); return 2; }
    if (make_directory(output_dir) != 0) { free(output_dir); return 2; }

    int rc = input_dir ? process_directory(input_dir, output_dir) : process_file(input_file, output_dir);
    free(output_dir);
    return rc == 0 ? 0 : 1;
}
