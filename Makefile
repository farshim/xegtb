CXX      ?= clang++
CXXFLAGS ?= -std=c++20 -O3 -march=native -DNDEBUG -Wall -Wextra -Wno-unused-parameter
LDFLAGS  ?= -pthread

SRC := src/mixed.cpp src/solver.cpp src/stats.cpp src/verify.cpp src/probe.cpp src/brute.cpp \
        src/policy.cpp src/kqkr.cpp src/kqkbb.cpp src/kqkk.cpp src/kqkkcap.cpp \
        src/kings.cpp src/general.cpp src/explore.cpp src/serve.cpp \
        src/io.cpp src/main.cpp
OBJ := $(SRC:.cpp=.o)
HDR := src/geometry.hpp src/index.hpp src/indexbb.hpp src/indexkk.hpp \
        src/movegen.hpp src/table.hpp src/explore.hpp src/general.hpp

all: egtb kqk krk kbbk kbnk

egtb: $(OBJ)
	$(CXX) $(CXXFLAGS) -o $@ $(OBJ) $(LDFLAGS)

# One binary, several endgames.  Invoked under one of these names it defaults
# to the matching --endgame; under its own name, to KQK.
kqk: egtb
	ln -sf egtb kqk
krk: egtb
	ln -sf egtb krk
kbbk: egtb
	ln -sf egtb kbbk
kbnk: egtb
	ln -sf egtb kbnk

%.o: %.cpp $(HDR)
	$(CXX) $(CXXFLAGS) -c -o $@ $<

test: egtb
	./egtb selftest --max 8

clean:
	rm -f $(OBJ) egtb kqk krk kbbk kbnk

.PHONY: all test clean
