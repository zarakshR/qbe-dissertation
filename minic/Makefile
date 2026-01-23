BIN = minic

MINIC = ./minic
QBE = ../qbe

CFLAGS += -g -Wall

$(BIN): yacc minic.y
	./yacc minic.y
	$(CC) $(CFLAGS) -o $@ y.tab.c

clean:
	rm -f yacc minic y.*
	rm -f test/out/*

test/out/%: test/% $(BIN)
	mv $< $@

test/%.qbe: test/%.c $(BIN)
	cat $< | $(MINIC) > $@

test/%.s: test/%.qbe
	$(QBE) $< > $@

test/%: test/%.s
	$(CC) $< -o $@

.PHONY: clean
