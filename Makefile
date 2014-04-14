all: test-map

test-map: $(wildcard src/*.rs)
	rustc --test src/lib.rs -g -o test-map

test: test-map
	./test-map

bench: test-map
	./test-map --bench
