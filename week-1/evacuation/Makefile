FLAGS:=-pipe -O2 -std=c++0x -g
#-DDEBUG
all: evacuation evacuation_d

evacuation: evacuation.cc
	g++  $(FLAGS) evacuation.cc   -lm -o ./bin/evacuation

evacuation_d: evacuation.cc
	g++  $(FLAGS) evacuation.cc -DDEBUG   -lm -o ./bin/evacuation_d
