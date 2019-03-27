plugin = prunessa
test_bin = loop

all:
	bapbuild -clean
	bapbuild $(plugin).plugin
	bapbundle install $(plugin).plugin

clean:
	bapbuild -clean
	unlink $(plugin).plugin || true
