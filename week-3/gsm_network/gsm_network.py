#!/usr/bin/env python3

class Gsm:

    def __init__(self,n,m,relations):
        self.n = n
        self.m = m
        self.relations = []

    def __str__(self):
        __repr__(self)

    def __repr__(self):
        print("<n :%d,m:%d> \n %s "%(g.n,g.m,g.relations))

    @staticmethod
    def read():
        n,m = map(int, input().split())
        relations = [list(map(int, input().split())) for i in range(m) ]
        return Gsm(n,m,relations)

    @staticmethod
    def simple_test():
        g = Gsm(3,3,[[1,2],[2,3],[1,3]])


class Graph:
    
    def __init__(self,n,m,relations):
        pass

    def foo(self):
        pass
    

if __name__ == "__main__":
    g = Gsm.read()

Gsm.simple_test()
