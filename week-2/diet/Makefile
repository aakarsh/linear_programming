FLAGS:=-pipe -O2 -std=c++0x -g
#-DDEBUG
all: diet diet_d

diet: diet.cc
	g++  $(FLAGS) diet.cc   -lm -o ./bin/diet

diet_d: diet.cc
	g++  $(FLAGS) diet.cc -DDEBUG   -lm -o ./bin/diet_d

test: simplex.py stress.py
	cp simplex.py ./sandbox/
	cp stress.py ./sandbox/
	cd ./sandbox/ && ./stress.py
