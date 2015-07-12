#
# vim: noet sw=4 ts=4
#

SOURCES=$(wildcard *.m)

all : tags pzasm pzllvm

pzasm : $(SOURCES)
	mmc --make $@

pzllvm : $(SOURCES)
	mmc --make $@

tags : $(SOURCES)
	mtags $(SOURCES)

.PHONY: clean
clean :
	rm -rf Mercury tags pzasm pzllvm *.err *.mh

