OCAML = ocamlc
OCAMLFLAGS = -g
FILES = ast.ml evaluateur.ml types.ml tests.ml
EXEC = tests

.PHONY: all clean run

all: $(EXEC)

$(EXEC): $(FILES)
	$(OCAML) $(OCAMLFLAGS) -o $(EXEC) $(FILES)

clean:
	rm -f *.cmo *.cmi $(EXEC)

run: $(EXEC)
	./$(EXEC)
