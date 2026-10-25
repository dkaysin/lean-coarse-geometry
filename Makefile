# Shortcuts for building the library and the blueprint. `make` lists the targets.

PORT ?= 8000

# The blueprint is extracted again only if one of these changed since the stamp.
LEAN_SRCS := $(shell find Coarse CoarseBlueprint -name '*.lean') Coarse.lean CoarseBlueprint.lean \
	lakefile.toml lake-manifest.json lean-toolchain
EXTRACTED := .lake/build/blueprint/stamp

.DEFAULT_GOAL := help
.PHONY: help cache build check mk_all blueprint web pdf serve frontier status sorries clean-blueprint

help: ## List the targets
	@grep -E '^[a-z_-]+:.*## ' $(MAKEFILE_LIST) | awk -F ':.*## ' '{printf "  %-16s %s\n", $$1, $$2}'

cache: ## Download Mathlib's compiled files
	lake exe cache get

build: ## Build the library
	lake build

check: ## What CI checks: build with warnings as errors, root import file up to date
	lake build --wfail
	lake exe mk_all --check

mk_all: ## Regenerate Coarse.lean and CoarseBlueprint.lean
	lake exe mk_all

blueprint: $(EXTRACTED) ## Build the tags and extract the blueprint to .lake/build/blueprint

$(EXTRACTED): $(LEAN_SRCS)
	lake build CoarseBlueprint :blueprint
	touch $@

web: blueprint ## Render the blueprint web page to blueprint/web
	leanblueprint web
	python3 scripts/blueprint_links.py

pdf: blueprint ## Render the blueprint pdf to blueprint/print/print.pdf
	leanblueprint pdf

serve: web ## Render and serve the web blueprint at http://localhost:8000 (PORT=… to change)
	python3 -m http.server $(PORT) --directory blueprint/web

frontier: ## List the frontier, nodes awaiting review, sorried and blocked nodes (no build)
	python3 scripts/blueprint_frontier.py

status: blueprint ## List the state of every blueprint node
	python3 scripts/blueprint_frontier.py --all

sorries: ## List every sorry in the library
	@grep -rn --include='*.lean' -w sorry Coarse || echo "No sorry."

clean-blueprint: ## Remove the rendered blueprint
	rm -rf blueprint/web blueprint/print blueprint/lean_decls
