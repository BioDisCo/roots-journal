.DEFAULT_GOAL := check
.PHONY: check check-offline check-sources cache paper check-all

check: check-sources
	$(MAKE) cache
	$(MAKE) check-offline

cache:
	cd lean && lake exe cache get

check-offline: check-sources
	cd lean && lake build
	cd lean && lake env lean CheckAxioms.lean
	python3 scripts/check_badges.py

check-sources:
	python3 scripts/check_badges.py --sources-only

paper:
	cd manuscript && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

check-all: check
	$(MAKE) paper
