########################################################################
# EECS 578  Mini-project (SystemVerilog Assertion)
########################################################################

VCS = vcs
VCSFLAGS = +v2k -sverilog -line -full64

DESIGN = arbiter.v
TESTBENCH = test_arbiter.sv

all: simv

simv: $(TESTBENCH) $(DESIGN)
	$(VCS) $(VCSFLAGS) $(TESTBENCH) $(DESIGN) -o simv

dve: $(TESTBENCH) $(DESIGN)
	$(VCS) $(VCSFLAGS) $(TESTBENCH) $(DESIGN) -o dve -R -gui

run: simv
	./simv

.PHONY: clean
clean:
	rm -rf csrc DVEfiles dve.daidir simv.daidir dve.vdb simv.vdb
	rm -f dve simv
	rm -f inter.vpd ucli.key

