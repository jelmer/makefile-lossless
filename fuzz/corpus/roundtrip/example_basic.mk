PYTHON = python3

.PHONY: all

all: build

build:
	$(PYTHON) setup.py build
