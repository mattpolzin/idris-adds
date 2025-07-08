
idris2 ?= idris2

PACKAGE = idris-adds.ipkg

all: build

.PHONY: build

build:
	$(idris2) --build $(PACKAGE)

.PHONY: clean

clean:
	$(idris2) --clean $(PACKAGE)

.PHONY: install

install:
	$(idris2) --install $(PACKAGE)

.PHONY: install-with-src

install-with-src:
	$(idris2) --install-with-src $(PACKAGE)
