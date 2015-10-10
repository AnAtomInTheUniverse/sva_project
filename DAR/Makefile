########################################################################
# EECS 578  Mini-project (SystemVerilog Assertion)
########################################################################

VCS = vcs
VCSFLAGS = +v2k -sverilog -line -full64 +incdir+./include -l ./reports/vcs.log

DESIGN = design/audio_app.v design/delay_line.v design/delay_prgrm.v
TESTBENCH = testbench/audio_app.test_top.sv

all: simv

simv: $(TESTBENCH) $(DESIGN)
	$(VCS) $(VCSFLAGS) $(TESTBENCH) $(DESIGN) -o ./obj/simv

dve: $(TESTBENCH) $(DESIGN)
	$(VCS) $(VCSFLAGS) $(TESTBENCH) $(DESIGN) -o ./obj/dve -R -gui

run: simv
	./obj/simv -l reports/simv.log

.PHONY: clean
clean:
	rm -rf csrc DVEfiles
	rm -rf obj/* reports/*
	rm -f inter.vpd ucli.key

