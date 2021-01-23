stardust : sdml/Stardust.grm sources.cm
	/usr/local/smlnj/bin/ml-build sources.cm Stardust.main stardust

clean :
	rm stardust.amd64-darwin 2> /dev/null || true
	rm -rf .cm */.cm || true

sdml/Stardust.grm : sdml/Stardust.silly.grm sdml/silly
	cd sdml && ./silly
