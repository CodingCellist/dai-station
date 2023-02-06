IDRIS2 ?= idris2

DEPS := -p contrib

SRCDIR = src
SRCS := $(wildcard $(SRCDIR)/*.idr)
SRCS += $(wildcard $(SRCDIR)/**/*.idr)
SRCS += $(wildcard $(SRCDIR)/**/**/*.idr)
SRCS += $(wildcard $(SRCDIR)/**/**/**/*.idr)

TRGT = dai

all: $(TRGT)

$(TRGT): $(SRCS)
	$(IDRIS2) --build $(TRGT).ipkg

build: $(SRCS)
	$(IDRIS2) --build $(TRGT).ipkg

check: $(SRCS)
	cd $(SRCDIR)
	$(IDRIS2) $(DEPS) --check $^

install: build
	$(IDRIS2) --install $(TRGT).ipkg

.PHONY: check clean install test

test:
	$(MAKE) -C tests only=$(only) except=$(except) IDRIS2=${IDRIS2}

clean:
	$(RM) -r build src/build
	@find . -type f -name '*.idr~' -delete

