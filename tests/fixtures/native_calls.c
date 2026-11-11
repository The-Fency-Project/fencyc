#include <stdarg.h>
#include <stdint.h>
#include <string.h>

int64_t native_apply(int64_t (*callback)(int64_t), int64_t value) {
    return callback(value) + 100;
}

int native_check(int marker, ...) {
    va_list args;
    va_start(args, marker);
    int signed_byte = va_arg(args, int);
    int unsigned_short = va_arg(args, int);
    double real = va_arg(args, double);
    int64_t a = va_arg(args, int64_t);
    int64_t b = va_arg(args, int64_t);
    int64_t c = va_arg(args, int64_t);
    int64_t d = va_arg(args, int64_t);
    const char *text = va_arg(args, const char *);
    va_end(args);
    return marker == 9 && signed_byte == -7 && unsigned_short == 65535 &&
           real == 1.5 && a == 10 && b == 20 && c == 30 && d == 40 &&
           strcmp(text, "tail") == 0;
}
