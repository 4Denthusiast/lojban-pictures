CFLAGS = `idris --include`

default: src/*.idr src/timer.o src/graphics.o
	idris -p lightyear -p sdl2 -p effects -p contrib --sourcepath src -i src src/Main.idr -o pretty
