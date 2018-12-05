default: src/*.idr
	idris -p lightyear -p sdl2 -p effects --sourcepath src -i src src/Main.idr -o pretty
