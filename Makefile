all: test-map

test-map: $(wildcard src/*.rs)
	rustc --test src/mod.rs -g -o test-map

test: test-map
	./test-map
