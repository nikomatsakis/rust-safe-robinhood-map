all:
	rustc --test src/mod.rs

test: all
	./mod
