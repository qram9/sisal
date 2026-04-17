# Sisal silicon test suite
# Each test: compile (gen + harness), run, check exit code.

SISAL := ../../_build/default/src/main.exe
CXX   := clang++
CXXFLAGS := -std=c++17 -O1 -I.

TESTS := if_one if_elseif aa negate_dv pick_dv

.PHONY: all clean regen $(TESTS)

all: $(TESTS)
	@echo ""
	@echo "All silicon tests passed."

$(TESTS): %: %_gen.cpp test_%.cpp
	@$(CXX) $(CXXFLAGS) $^ -o $@_bin
	@./$@_bin
	@echo ""

regen:
	$(SISAL) --c ../../test/if_one.sis       > if_one_gen.cpp
	$(SISAL) --c ../../test/if_elseif.sis    > if_elseif_gen.cpp
	$(SISAL) --c ../../test/aa.sis           > aa_gen.cpp
	$(SISAL) --c ../../test/negate_dv.sis    > negate_dv_gen.cpp
	$(SISAL) --c ../../test/pick_dv.sis      > pick_dv_gen.cpp

clean:
	rm -f $(addsuffix _bin, $(TESTS))
