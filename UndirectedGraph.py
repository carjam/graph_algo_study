#!/usr/bin/env python3
import sys
sys.path.append('../../algorithms')
import utility

from collections import defaultdict
import heapq
import math

from unionFind import DisjointSet

class UndirectedGraph: 
    def __init__(self, v): 
        self.edges = defaultdict(list) #adjacency map 
        self.edgeDist = defaultdict(dict)
        self.verts = v #vertices
  
    def addEdge(self, u, v, distance = 0): 
        self.edges[u].append(v) # u->v
        self.edges[v].append(u) # u->v
        self.edgeDist[u][v] = distance # u->v
        self.edgeDist[v][u] = distance # u->v
        
    def hasEdge(self, u, v):
        return v in self.edges[u]
        
    def removeEdge(self, u, v):
        self.edges[u].remove(v)
        self.edges[v].remove(u)
        self.edgeDist[u].pop(v, None)
        self.edgeDist[v].pop(u, None)
        
    # MST Minimum Spanning Tree - subset of edges in undirected graph w/ all vertices w/out any circuits
    # O(E log V) - using union find
    # https://www.geeksforgeeks.org/kruskals-minimum-spanning-tree-algorithm-greedy-algo-2/
    @staticmethod
    @utility.profile 
    def kruskalMST(graf):
        edges = sorted([(u, v, graf.edgeDist[u][v]) for u in graf.edges for v in graf.edges[u]], key = lambda a: a[2])
        ds = DisjointSet()
        for node in graf.verts:
            ds.makeSet(node)
      
        res, i, e = [], 0, 0
        while e < len(graf.verts) - 1: # max edges == V-1
            u, v, w = edges[i]
            x, y = ds.find(u), ds.find(v)

            if x != y: 
                e += 1     
                ds.union(x, y)
                res.append([u,v,w])
            i += 1

        return res
        
    # MST Minimum Spanning Tree - subset of edges in undirected graph w/ all vertices w/out any circuits
    # !!!Use when you have a graph with lots of edges - dense graph!!!
    # Note the similarity to Dijkstra
    # O(E + V log V) amortized time w/ heap
    # https://www.youtube.com/watch?v=oP2-8ysT3QQ
    # https://leetcode.com/problems/cheapest-flights-within-k-stops/discuss/359596/prims-algorithm-for-finding-minimum-spanning-treepython
    @staticmethod
    @utility.profile 
    def primsMST(graf, start):
        q, seen, distance, parent = [], set(), {}, defaultdict(int)
        for v in graf.verts:
            dist = 0 if v == start else math.inf
            heapq.heappush(q, (dist, v))
        
        res = set()
        while q:
            _, u = heapq.heappop(q)
            if u in seen:
                edge = tuple(sorted([parent[u], u]))
                dist = distance[u]
                res.add((edge, dist))
                continue
            seen.add(u)
            
            for v in graf.edgeDist[u]:
                dist = graf.edgeDist[u][v]
                if v not in distance or dist < distance[v]:
                    distance[v] = dist
                    parent[v] = u
                    heapq.heappush(q, (dist, v))
        
        return res


@utility.profile       
def main():
    #Kruskal's MST
    print('Kruskals Minimal Spanning Tree:')
    g = UndirectedGraph([i for i in range(4)]) 
    g.addEdge(0, 1, 10)
    g.addEdge(0, 2, 6)
    g.addEdge(0, 3, 5)
    g.addEdge(1, 3, 15)
    g.addEdge(2, 3, 4)
    res = UndirectedGraph.kruskalMST(g)
    cost = 0
    for u,v,weight in res: 
        print ("%d -- %d == %d" % (u,v,weight))
        cost += weight
    print('Total cost=', cost)
    assert(res == [[2, 3, 4], [0, 3, 5], [0, 1, 10]])
    assert(cost == 19)
    
    #Prims's MST
    print("\nPrims Minimal Spanning Tree:")
    g = UndirectedGraph([i for i in range(4)]) 
    g.addEdge(0, 1, 10)
    g.addEdge(0, 2, 6)
    g.addEdge(0, 3, 5)
    g.addEdge(1, 3, 15)
    g.addEdge(2, 3, 4)
    edges = UndirectedGraph.primsMST(g, 0)
    cost = 0
    for e,w in edges: 
        print (e[0], ' -- ', e[1], ' = ', w)
        cost += w
    assert(cost == 19)
    
    
if __name__ == "__main__":
    main()

