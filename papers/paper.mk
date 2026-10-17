# bins
LATEXMK ?= latexmk
LATEXMKFLAGS ?=
LATEXPAND ?= latexpand
PDFLATEX ?= pdflatex
TEXFMT ?= tex-fmt
DISTDIR ?= dist

MAIN := $(VENUE)-$(NAME)
ARXIV := arxiv-$(NAME)
DRIVERS ?= $(sort $(wildcard *-$(NAME).tex *-$(NAME)-*.tex))
PDFS := $(DRIVERS:.tex=.pdf)
DIST := $(PDFS)
# NAME.bib is exported from zotero
SRCS := $(filter-out $(NAME).bib,$(wildcard *.tex *.sty *.bib))

all: $(PDFS)

$(PDFS): %.pdf: %.tex FORCE
	$(LATEXMK) $(LATEXMKFLAGS) $<

cont:
	$(LATEXMK) $(LATEXMKFLAGS) -pvc $(MAIN).tex

check-pages: $(MAIN).pdf
ifdef PAGELIMIT
	@n=$$(sed -n 's/^\\newlabel{body-end}{{[^}]*}{\([^}]*\)}.*/\1/p' $(MAIN).aux | sed 's/.*://'); \
	test -n "$$n" || { echo "error: no body-end label in $(MAIN)" >&2; exit 1; }; \
	echo "$(MAIN): body $$n/$(PAGELIMIT) pages (+refs)"; \
	if [ -n "$$GITHUB_STEP_SUMMARY" ]; then echo "$(MAIN): body $$n/$(PAGELIMIT) pages (+refs)" >> "$$GITHUB_STEP_SUMMARY"; fi; \
	if [ "$$n" -gt "$(PAGELIMIT)" ]; then \
	  msg="$(MAIN): body is $$n pages, over the limit of $(PAGELIMIT)"; \
	  if [ -n "$(STRICT)" ]; then echo "error: $$msg" >&2; exit 1; fi; \
	  if [ -n "$$GITHUB_ACTIONS" ]; then echo "::warning::$$msg"; else echo "warning: $$msg" >&2; fi; \
	fi
else
	@echo "$(MAIN): no PAGELIMIT set"
endif

ifneq ($(wildcard $(ARXIV).tex),)
DIST += $(ARXIV).tar.gz

arxiv: $(ARXIV).tar.gz

$(ARXIV).tar.gz: $(ARXIV).pdf FORCE
	@stage=$$(mktemp -d) && trap 'rm -rf "$$stage"' EXIT && \
	$(LATEXPAND) --empty-comments --expand-bbl $(ARXIV).bbl -o "$$stage/$(ARXIV).tex" $(ARXIV).tex && \
	sed -n 's/^INPUT //p' $(ARXIV).fls | grep -v '^/' | sed 's|^\./||' \
	  | grep -v '^$(ARXIV)\.' | grep -vE '\.(tex|bib|bbl)$$' | sort -u \
	  | xargs -I{} cp {} "$$stage/" && \
	tar -czf $@ -C "$$stage" $$(ls "$$stage") && \
	echo "$@: $$(ls "$$stage" | tr '\n' ' ')"

check-arxiv: $(ARXIV).tar.gz
	@tmp=$$(mktemp -d) && trap 'rm -rf "$$tmp"' EXIT && \
	tar -xzf $< -C "$$tmp" && cd "$$tmp" && \
	{ $(PDFLATEX) -interaction=nonstopmode -halt-on-error $(ARXIV).tex > /dev/null \
	  && $(PDFLATEX) -interaction=nonstopmode -halt-on-error $(ARXIV).tex > /dev/null \
	  || { tail -40 $(ARXIV).log; exit 1; }; } && \
	! grep -E 'There were undefined|Citation .* undefined' $(ARXIV).log && \
	echo "$<: builds standalone"
else
arxiv check-arxiv:
	@echo "no $(ARXIV).tex"
endif

format:
	$(TEXFMT) $(SRCS)

check-format:
	$(TEXFMT) --check $(SRCS)

zip: $(MAIN).zip

$(MAIN).zip: $(MAIN).pdf FORCE
	rm -f $@
	zip $@ $(filter-out $(filter-out $(MAIN).tex,$(DRIVERS)),$(wildcard *.tex)) \
	  $(wildcard *.sty *.cls *.bib) $(filter-out $(PDFS),$(wildcard *.pdf)) $(MAIN).bbl

dist: all check-pages check-arxiv
	rm -rf $(DISTDIR) && mkdir -p $(DISTDIR)
	cp $(DIST) $(DISTDIR)/

clean:
	$(LATEXMK) -C $(DRIVERS)
	rm -rf $(DISTDIR) $(MAIN).zip $(ARXIV).tar.gz

FORCE:

.PHONY: all cont check-pages arxiv check-arxiv format check-format zip dist clean FORCE
