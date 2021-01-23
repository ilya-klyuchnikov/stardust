#
# For the time being, run mlyacc/mllex via SML/NJ + CM.
#

# Targets:
#
#     nj           build under SML/NJ
#     mlton        build under MLton (profiling off)
#     mlton.prof   build under MLton (profiling on)

all : nj mlton

clean :
	rm stardust-nj stardust 2> /dev/null || true
	rm -rf .cm */.cm || true

mlton : stardust

nj : stardust-nj

sdml/Stardust.grm : sdml/Stardust.silly.grm sdml/silly
	cd sdml && ./silly

stardust-nj : sdml/Stardust.grm sources.cm
	echo 'CM.make"sources.cm"; Jerseymain.export "stardust-nj";' | /usr/local/smlnj/bin/sml

stardust.prof : sdml/Stardust.grm sources.cm
	./jcm2mlb sources
	mlton \
	      -drop-pass deepFlatten \
	      -profile time \
	      -output stardust.prof \
	      sources.mlb

stardust : sdml/Stardust.grm sources.cm
	./jcm2mlb sources
	mlton \
	      -drop-pass deepFlatten \
	      -output stardust \
	      sources.mlb
