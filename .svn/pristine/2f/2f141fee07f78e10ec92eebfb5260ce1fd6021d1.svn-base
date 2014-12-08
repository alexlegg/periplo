SUBDIRS = src

bin_PROGRAMS = periplo
AM_CPPFLAGS = $(config_includedirs)
ACLOCAL_AMFLAGS = -I m4

periplo_SOURCES = src/bin/periplo.C
periplo_LDADD = src/libperiplo.la -lgmpxx
