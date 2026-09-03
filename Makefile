all: rocq # plugin

rocq: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

install: rocq # plugin
	$(MAKE) -f Makefile.rocq install
	# $(MAKE) -f Makefile.plugin install

doc : Makefile.rocq
	$(MAKE) -f Makefile.rocq html

uninstall: rocq # plugin
	$(MAKE) -f Makefile.rocq uninstall
	# $(MAKE) -f Makefile.plugin uninstall

.PHONY: plugin

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq clean
