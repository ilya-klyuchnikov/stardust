#
# For the time being, run mlyacc/mllex via SML/NJ + CM.
#

# Targets:
#
#     nj           build under SML/NJ

all : nj

clean :
	rm stardust-nj stardust 2> /dev/null || true
	rm -rf .cm */.cm || true

nj : stardust-nj

sdml/Stardust.grm : sdml/Stardust.silly.grm sdml/silly
	cd sdml && ./silly

stardust-nj : sdml/Stardust.grm sources.cm
	echo 'CM.make"sources.cm"; Jerseymain.export "stardust-nj";' | /usr/local/smlnj/bin/sml
