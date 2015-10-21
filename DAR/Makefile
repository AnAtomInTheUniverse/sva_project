########################################################################
# EECS 578  Mini-project (SystemVerilog Assertion)
########################################################################

VCS = vcs
VCSFLAGS = +v2k -sverilog -line -full64 +incdir+./include 
#-l ./reports/vcs.log

DESIGN = design/audio_app.v design/delay_line.v design/delay_prgrm.v
TESTBENCH = testbench/audio_app.test_top.sv
#TESTBENCH = testbench/basic_dar_test.sv

all: simv

simv: $(TESTBENCH) $(DESIGN)
	$(VCS) $(VCSFLAGS) $(TESTBENCH) $(DESIGN) -o simv

dve: $(TESTBENCH) $(DESIGN)
	$(VCS) $(VCSFLAGS) $(TESTBENCH) $(DESIGN) -o dve -R -gui

run: simv
	./simv -l reports/simv.log

.PHONY: clean
clean:
	rm -rf csrc DVEfiles
	rm -rf obj/* reports/*
	rm -f inter.vpd ucli.key

