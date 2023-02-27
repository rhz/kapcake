COQMFFLAGS := -Q . KapCake

# ALLVFILES := NatMap.v NatSet.v Rel.v LibTactics.v Tactics.v SiteGraph.v
ALLVFILES := finmap_ext.v mathcomp_ext.v ContactGraph.v Hom.v

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
