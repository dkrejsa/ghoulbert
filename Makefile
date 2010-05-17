
ifeq ($(GOARCH),)
$(error GOARCH, GOROOT, and GOOS must be defined. See http://golang.org/doc/install.html)
endif

ifeq ($(GOARCH),386)
GO_COMPILER = 8g
GO_LINKER = 8l
GO_OBJEXT = 8
endif

ifeq ($(GOARCH),amd64)
GO_COMPILER = 6g
GO_LINKER = 6l
GO_OBJEXT = 6
endif

ifeq ($(GOARCH),arm)
GO_COMPILER = 5g
GO_LINKER = 5l
GO_OBJEXT = 5
endif

ifeq ($(GO_COMPILER),)
$(error GO_COMPILER not known)
endif
ifeq ($(GO_LINKER),)
$(error GO_LINKER not known)
endif
ifeq ($(GO_OBJEXT),)
$(error GO_OBJEXT not known)
endif

RM = rm -f

GHOULBERT_SOURCES = ghoulbert.go

GHOULBERT_OBJS = $(patsubst %.go,%.$(GO_OBJEXT),$(GHOULBERT_SOURCES))

ghoulbert : $(GHOULBERT_OBJS)
	$(GO_LINKER) -o $@ $^

%.$(GO_OBJEXT) : %.go
	$(GO_COMPILER) $<

.PHONY : clean

clean :
	$(RM) ghoulbert $(GHOULBERT_OBJS)
