#!/usr/bin/env python3
import sys
sys.path.append('../../algorithms')
import utility
from collections import defaultdict

# all ops O(n) worst case, amortized O(1)
class DisjointSet:
    def __init__(self):
        self.parents = defaultdict()
        self.ranks = defaultdict(int)
    
    def makeSet(self, val):
        self.parents[val] = val
        self.ranks[val] = 0

    def find(self, node):
        if self.parents[node] == node:
            return node
        self.parents[node] = self.find(self.parents[node]) #path compression
        return self.parents[node]
    
    def union(self, x, y):
        xset = self.find(x)
        yset = self.find(y)
        if xset == yset:
            return #graph has cycle
        
        if self.ranks[xset] >= self.ranks[yset]:
            self.ranks[xset] = self.ranks[xset] + 1 if self.ranks[xset] == self.ranks[yset] else self.ranks[xset]
            self.parents[xset] = yset
        else:
            self.parents[yset] = xset

@utility.profile       
def main():
    M=[[1,1,0],[1,1,0],[0,0,1]]
    n=len(M)
    ds=DisjointSet()

    for ii in range(n):
        ds.makeSet(ii)

    for ii in range(n):
        for jj in range(n):
            if M[ii][jj] == 1 and ii != jj:
                ds.union(ii, jj)
    cnt=0
    for ii in range(n):
        if ds.find(ds.parents[ii]) == ii:
            cnt += 1
    
    print('Result: ' + str(cnt) + ", " + str(cnt==2))
    assert(cnt == 2)
    
	
if __name__ == "__main__":
    main()

