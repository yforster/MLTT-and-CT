.PHONY: clean all

all: main.pdf

%.pdf: %.tex
	rubber -f --pdf -s $<
	rubber-info --check $<

clean:
	rubber --clean main.pdf
