SUBDIRS = parsers egraph satsolvers cnfizers simplifiers proof api sorts 

noinst_LTLIBRARIES = libperiplo.la

if WANT_LIBRARY
lib_LTLIBRARIES = libperiplolibrary.la
endif

libperiplo_la_SOURCES =
libperiplo_la_LIBADD = parsers/libparsers.la \
		       satsolvers/libsatsolvers.la \
		       cnfizers/libcnfizers.la \
		       simplifiers/libsimplifiers.la \
		       proof/libproof.la \
		       egraph/libegraph.la \
		       sorts/libsorts.la \
		       api/libapi.la 

libperiplolibrary_la_SOURCES = 
libperiplolibrary_la_LIBADD = satsolvers/libsatsolvers.la \
		       cnfizers/libcnfizers.la \
		       simplifiers/libsimplifiers.la \
		       proof/libproof.la \
		       egraph/libegraph.la \
		       sorts/libsorts.la \
		       api/libapi.la 

include_HEADERS = common/Global.h common/SplayTree.h common/Otl.h \
		  minisat/core/SolverTypes.h minisat/mtl/IntTypes.h \
		  minisat/mtl/Alg.h minisat/mtl/Vec.h minisat/mtl/XAlloc.h \
		  minisat/mtl/Map.h minisat/mtl/Alloc.h minisat/mtl/Queue.h \
		  minisat/mtl/Heap.h minisat/utils/Options.h minisat/utils/ParseUtils.h
