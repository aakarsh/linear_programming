FLAGS:=-pipe -O2 -std=c++0x -g
#-DDEBUG
all: airline_crews airline_crews_d

airline_crews: airline_crews.cc
	g++  $(FLAGS) airline_crews.cc   -lm -o ./bin/airline_crews

airline_crews_d: airline_crews.cc
	g++  $(FLAGS) airline_crews.cc -DDEBUG   -lm -o ./bin/airline_crews_d
