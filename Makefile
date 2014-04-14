all: test-map

test-map: $(wildcard src/*.rs src/*/*.rs)
	rustc --test src/lib.rs -g -o test-map

test-map-opt: $(wildcard src/*.rs src/*/*.rs)
	rustc --test src/lib.rs -O -o test-map-opt

test: test-map
	./test-map

bench: test-map-opt
	./test-map --bench
