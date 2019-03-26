plugin = myssa
test_bin = loop

all:
	bapbuild -clean
	bapbuild $(plugin).plugin
	bapbundle install $(plugin).plugin
	bap $(test_bin) --pass=$(plugin) -d
