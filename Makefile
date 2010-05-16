GO_COMPILER = 6g
GO_LINKER = 6l
GO_OBJEXT = 6

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