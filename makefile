.PHONY: all build validate clean cache

all: build

cache:
	lake exe cache get

build:
	lake build PackageCalculus

validate: build
	lake env lean scripts/axioms.lean

clean:
	rm -rf .lake/build/lib/lean/PackageCalculus .lake/build/lib/lean/PackageCalculus.olean
