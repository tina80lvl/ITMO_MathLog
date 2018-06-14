CXXFLAGS+=-std=c++14 -Wall -O2
CXX=g++

all: out out/main.o

run: out out/main.o
	./out/main.o

out/main.o: src/main.cpp 
	$(CXX) $^ $(CXXFLAGS) -o out/main.o

pack: 
	zip hw1.zip -r Makefile src

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f src/parser/*.c src/parser/*.h