.PHONY: test clean

SHELL    := /bin/bash

MEZZODIR := ../..
MEZZO    := $(MEZZODIR)/mezzo

test:
# Make sure mezzo is up-to-date.
	$(MAKE) -C $(MEZZODIR)
# Run each test file.
# Output is logged to f.out; errors are logged to f.err;
# the exit status is logged to f.xit.
# We expect every source file to contain a Success or Failure comment,
# which indicates the expected result.
# If the interpreter terminates normally and produces one last line of
# output, say 13, then we check that the source file contains the
# comment "Success: 13".
# If the interpreter terminates abnormally, then we check that the
# source file contains a comment of the form "Failure: reason", and
# we look for "reason" in the error output.
	@for f in *.mz ; do \
	  if ! $(MEZZO) $$f >/dev/null 2>$${f%.mz}.err ; then \
	    echo [PROBLEM] $$f was rejected by the Mezzo type-checker ; \
	    continue ; \
	  fi ; \
	  if ! grep -q -e "\(Success\|Failure\)" $$f ; then \
	    echo "[PROBLEM] $$f does not contain a Success or Failure comment" ; \
	    continue ; \
	  fi ; \
	  OCAMLRUNPARAM=b $(MEZZO) -i $$f >$${f%.mz}.out 2>$${f%.mz}.err ; \
	  echo $$? >$${f%.mz}.xit ; \
	  if [[ `cat $${f%.mz}.xit` == 0 ]] ; then \
	    echo The interpreter terminated normally >/dev/null ; \
	    actual=`tail -1 $${f%.mz}.out` ; \
	    if grep -q "Success: $$actual" $$f ; then \
	      echo "[OK] $$f" ; \
	    else \
	      echo "[FAILED] $$f (got $$actual, expected a different result or a failure)" ; \
	    fi \
	  else \
	    echo The interpreter terminated abnormally >/dev/null ; \
	    if grep -q Failure $$f ; then \
	      reason=`sed --quiet "s/(\* Failure: \\(.*\\) \*)/\1/p" $$f` ; \
	      if grep -q "$$reason" $${f%.mz}.err ; then \
		echo "[OK] $$f" ; \
	      else \
		echo "[FAILED] $$f (expected $$reason, got a different failure)" ; \
	      fi \
	    else \
	      echo "[FAILED] $$f (did not expect a failure)" ; \
	    fi \
	  fi \
	done

clean:
	rm -f *~
	rm -f *.{out,err,xit}
