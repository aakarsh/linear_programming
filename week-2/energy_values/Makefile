FLAGS:=-pipe -O2 -std=c++0x -g
#-DDEBUG
all: energy_values energy_values_d

energy_values: energy_values.cc
	g++  $(FLAGS) energy_values.cc   -lm -o ./bin/energy_values

energy_values_d: energy_values.cc
	g++  $(FLAGS) energy_values.cc -DDEBUG   -lm -o ./bin/energy_values_d
