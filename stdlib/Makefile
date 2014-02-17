.PHONY: all

all:
	$(shell rm -f MezzoStdLib.mllib)
	$(shell for a in *.mz; do echo mz_`basename $$a .mz` >> MezzoStdLib.mllib; done)
	@echo "MezzoStdLib.mllib generated"
