#include <fcntl.h>

// AT_NO_AUTOMOUNT & AT_EMPTY_PATH are Linux only, and then only with
// _GNU_SOURCE defined. At least compile on all operating systems.
#define AT_NO_AUTOMOUNT	0x800
#define AT_EMPTY_PATH   0x1000	

int scalanative_f_dupfd() { return F_DUPFD; }
int scalanative_f_getfd() { return F_GETFD; }
int scalanative_f_getfl() { return F_GETFL; }
int scalanative_f_getlk() { return F_GETLK; }
int scalanative_f_getown() { return F_GETOWN; }
int scalanative_f_setfd() { return F_SETFD; }
int scalanative_f_setfl() { return F_SETFL; }
int scalanative_f_setlk() { return F_SETLK; }
int scalanative_f_setlkw() { return F_SETLKW; }
int scalanative_f_setown() { return F_SETOWN; }

int scalanative_fcntl_at_eaccess() { return AT_EACCESS; }
int scalanative_fcntl_at_empty_path() { return AT_EMPTY_PATH; }
int scalanative_fcntl_at_no_automount() { return AT_NO_AUTOMOUNT; }
int scalanative_fcntl_at_removedir() { return AT_REMOVEDIR; }
int scalanative_fcntl_at_symlink_follow() { return AT_SYMLINK_FOLLOW; }
int scalanative_fcntl_at_symlink_nofollow() { return AT_SYMLINK_NOFOLLOW; }

int scalanative_o_append() { return O_APPEND; }
int scalanative_o_creat() { return O_CREAT; }
int scalanative_o_nonblock() { return O_NONBLOCK; }
int scalanative_o_rdonly() { return O_RDONLY; }
int scalanative_o_rdwr() { return O_RDWR; }
int scalanative_o_trunc() { return O_TRUNC; }
int scalanative_o_wronly() { return O_WRONLY; }
