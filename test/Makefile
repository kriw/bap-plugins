bins = ./bins/loop ./bins/test
disas = $(patsubst ./bins/%,./disas/%.bil,$(bins))
pair = $(patsubst ./bins/%,./disas/%.bil ./bins/%,$(bins))

.PHONY: all generate diff %_diff clean

all:
	./run.sh

generate: $(disas)

./disas/%.bil: %
	./ssa.sh $< --pass=prunessa > $@

clean:
	rm ./disas/*
