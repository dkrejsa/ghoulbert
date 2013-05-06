
ifeq ($(GOARCH),)
$(error GOARCH, GOROOT, and GOOS must be defined. See http://golang.org/doc/install.html)
endif

export GOPATH = $(shell pwd)

GO = go

RM = rm -f

GHOULBERT_SOURCES = ghoulbert.go

ghoulbert : $(GHOULBERT_SOURCES)
	$(GO) build 

.PHONY : clean

clean :
	$(GO) clean
