default: src/*.idr
	idris -p lightyear -p sdl2 -p effects -p contrib --sourcepath src -i src src/Main.idr -o pretty
