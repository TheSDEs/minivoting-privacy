# -*- Makefile -*-

# --------------------------------------------------------------------
ECROOT   ?=
ECCHECK  ?= config/runtest
ECARGS   ?= -I core -I Voting -I MiniVoting -I Helios -I Helios/Helios_mix -I Helios/Helios_hom -I Helios/Helios_create
ECCONF   := config/tests.config 
XUNITOUT ?= xunit.xml
CHECKS   ?= evoting

ifeq ($(ECROOT),)
else
PATH    := ${ECROOT}:${PATH}
endif

# --------------------------------------------------------------------
.PHONY: default check check-xunit

default:
	@echo "Usage: make <target> where <target> in [check|check-xunit]" >&2

check:
	$(ECCHECK) --bin-args="$(ECARGS)" $(ECCONF) $(CHECKS)

check-xunit:
	$(ECCHECK) --bin-args="$(ECARGS)" --xunit=$(XUNITOUT) $(ECCONF) $(CHECKS)
