#!/usr/bin/env python3
import sys
sys.path.append('../../algorithms')
import utility

from itertools import count
from collections import defaultdict
from collections import deque
from collections import Counter

import heapq
import math
import random

from unionFind import DisjointSet

import networkx as nx


class DirectedGraph: 
    def __init__(self, v): 
        self.edges = defaultdict(list) #adjacency map 
        self.edgeDist = defaultdict(dict)
        self.verts = v #vertices
  
    def addEdge(self, u, v, distance = 1): 
        self.edges[u].append(v) # u->v
        self.edgeDist[u][v] = distance # u->v
        
    def hasEdge(self, u, v):
        return v in self.edges[u]
        
    def removeEdge(self, u, v):
        self.edges[u].remove(v)
        self.edgeDist[u].pop(v, None)
        
    def removeVert(self, u):
        self.verts.remove(u)
        self.edges.pop(u, None)
        self.edgeDist.pop(u, None)
    

    '''
    ### SORTING ###
    '''
    def __sortEdges(graf, v, seen, ans): 
        if v in seen: #detect cycles
            return seen[v]
            
        seen[v] = False #passed by copy so changes propagate to caller
        for u in graf.edges[v]: #for all i's adjacent to v
            if not graf.__sortEdges(u, seen, ans):
                return False
  
        ans.appendleft(v)
        seen[v] = True
        return True
    
    # DFS sort (recursive)
    @staticmethod    
    def dfsTopologicalSort(graf): # DFS
        seen = {}
        ans=deque()
  
        for i in graf.verts: #alls vertices
            if not graf.__sortEdges(i, seen, ans):
                return [] #cycle present, cannot sort
        
        return ans

    # BFS sorting
    #"peeling the onion"
    @staticmethod
    def kahnsTopologicalSort(graf): 
        #assign number of incoming edges to each vertex
        in_degree = {v:0 for v in graf.verts}
        for v in graf.edges: 
            for u in graf.edges[v]: 
                in_degree[u] += 1
  
        #start w/ vertices w/out incoming edges
        q = deque()
        for v in graf.verts: 
            if in_degree[v] == 0: 
                q.append(v) 
  
        cnt = 0
        ans = deque()
        while q:
            v = q.popleft() 
            ans.append(v) 
            cnt += 1
  
            #reduce adjacent vetices by one and prime the queue
            for u in graf.edges[v]: 
                in_degree[u] -= 1
                if in_degree[u] == 0: 
                    q.append(u) 
  
  
        return ans if cnt==len(graf.verts) else deque()
    
    
    '''
    ### SHORTEST PATH ###
    '''

    '''
     Space  O(E + V) Time O(E + VlogE)
     https://gist.github.com/kachayev/5990802
     Special case of A* where heuristic distance to target is 0
     doesn't work for negative weights
     When tgt == None becomes Single Source Shortest Path
    '''  
    #@utility.profile
    # when tgt == None this becomes a Single Source Shortest Path
    @staticmethod
    def dijkStraHeap(graf, sourceVertex, tgt = None):
        q = []
        heapq.heappush(q, (0, sourceVertex, []))
        seen, distance, paths = set(), defaultdict(int), {}
        parent = defaultdict(int)
        parent[sourceVertex] = None
        for v in graf.verts:
            distance[v] = 0 if v == sourceVertex else math.inf
        
        while q:
            dist, v, path = heapq.heappop(q)
            if v in seen:
                continue
            seen.add(v)
            path = path + [v]
            paths[v] = path if v not in paths or len(path) < path[v] else path[v]
            if v == tgt:
                return (distance, paths)
            
            for adjacent in graf.edgeDist[v]:
                if adjacent in seen:
                    continue
                dist = graf.edgeDist[v][adjacent]
                newDist = distance[v] + dist
                if newDist < distance[adjacent]:
                    distance[adjacent] = newDist
                    parent[adjacent] = v
                    heapq.heappush(q, (newDist, adjacent, path))
        
        return (distance, paths) #if no tgt provided, return all distances
        
    #@utility.profile
    # when tgt == None this becomes a Single Source Shortest Path
    @staticmethod
    def aStar(graf, sourceVertex, tgt = None):
        q = []
        heapq.heappush(q, (0, 0, sourceVertex, []))
        seen, distance, paths = set(), defaultdict(int), {}
        parent = defaultdict(int)
        parent[sourceVertex] = None
        for v in graf.verts:
            distance[v] = 0 if v == sourceVertex else math.inf
        
        while q:
            _, dist, v, path = heapq.heappop(q)
            if v in seen:
                continue
            seen.add(v)
            path = path + [v]
            paths[v] = path if v not in paths or len(path) < path[v] else path[v]
            if v == tgt:
                return (distance, paths)
            
            for adjacent in graf.edgeDist[v]:
                if adjacent in seen:
                    continue
                dist = graf.edgeDist[v][adjacent]
                newDist = distance[v] + dist
                if newDist < distance[adjacent]:
                    distance[adjacent] = newDist
                    parent[adjacent] = v
                    heurDist = newDist #any heuristic to drive order of heap here
                    heapq.heappush(q, (heurDist, newDist, adjacent, path))
        
        return (distance, paths) #if no tgt provided, return all distances
        
    # https://en.wikipedia.org/wiki/Yen%27s_algorithm
    # https://github.com/guilhermemm/k-shortest-path/blob/master/k_shortest_paths.py
    # time O(KN(M+N\log N))
    # doesn't work on negative weights - (dijkstra)
    #@utility.profile
    @staticmethod
    def yensK(graf, source, tgt, K = 1):
        def getPathLen(edgeDist, path):
            length = 0
            if len(path) > 1:
                for i in range(len(path) - 1):
                    u = path[i]
                    v = path[i + 1]
                    length += edgeDist[u][v]
                    
            return length

        h = []
        c = count()
        origDist = graf.edgeDist.copy()
        length, path = DirectedGraph.dijkStraHeap(graf, source, tgt)
        lengths, paths = [length[tgt]], [path[tgt]]
        
        for i in range(1, K):
            # The spur node ranges from the first node to the next to last node in the previous k-shortest path.
            for j in range(len(paths[-1]) - 1):
                spurNode = paths[-1][j] # Spur node is retrieved from the previous k-shortest path, k − 1.
                rootPath = paths[-1][:j + 1] # The sequence of nodes from the source to the spur node of the previous k-shortest path.
               
                # Remove the links that are part of the previous shortest paths which share the same root path.
                edgesRemoved = []
                for p in paths:
                    if len(p) > j and rootPath == p[:j+1]:
                        u = p[j]
                        v = p[j + 1]
                        dist = graf.edgeDist[u][v]
                        graf.removeEdge(u, v)
                        edgesRemoved.append((u, v, dist))
               
                #remove rootPathNode from rootPath
                for n in range(len(rootPath) - 1):
                    node = rootPath[n]
                    for u in graf.edges:
                        for v in graf.edges[u]:
                            dist = graf.edgeDist[u][v]
                            graf.removeEdge(u, v)
                            edgesRemoved.append((u, v, dist))

                # Calculate the spur path from the spur node to the tgt.
                spurPathLen, spurPaths = DirectedGraph.dijkStraHeap(graf, spurNode, tgt)
                if tgt in spurPaths:
                    totalPath = rootPath[:-1] + spurPaths[tgt] # Entire path is made up of the root path and spur path.
                    totalPathLen = getPathLen(origDist, rootPath) + spurPathLen[tgt]                
                    heapq.heappush(h, (totalPathLen, next(c), totalPath)) # Add the potential k-shortest path to the heap.
               
                # Add back the edges and nodes that were removed from the graf.
                for u, v, dist in edgesRemoved:
                    graf.addEdge(u, v, dist)
                #restore nodes in rootPath to graf
                       
            if not h:
                # This handles the case of there being no spur paths, or no spur paths left.
                # This could happen if the spur paths have already been exhausted (added to A), 
                # or there are no spur paths at all - such as when both the source and tgt vertices 
                # lie along a "dead end".
                break
            # Add the lowest cost path becomes the k-shortest path.
            (l, _, p) = heapq.heappop(h)
            lengths.append(l)
            paths.append(p) 

        return (lengths, paths)

    # https://www.youtube.com/watch?v=-mOEd_3gTK0
    # https://www.geeksforgeeks.org/bellman-ford-algorithm-dp-23/
    # w/ Vectorization & caching - https://dzone.com/articles/algorithm-week-bellman-ford-1
    # unlike Dijkstra allows for DirectedGraphs w/ negative edges (ie. rewards & penalties for different paths)
    # https://www.youtube.com/watch?v=ozsuci5pIso&list=PLUl4u3cNGP61Oq3tWYp6V_F-5jb5L2iHb&index=17
    # O(V*E) & O(V)
    @staticmethod
    def bellmanFordSSSP(graf, src):
        dist, parent = defaultdict(int), {}
        for v in graf.verts:
            dist[v] = math.inf
        dist[src] = 0

        # Step 2: Relax all edges |V| - 1 times. Shortest path src to vertex can be at-most |V| - 1
        for _ in range(len(graf.verts) - 1):
            # Update dist value and parent index of the adjacent vertices of  
            # the picked vertex. Consider only those vertices which are still in  
            # queue  
            for u in graf.edges:
                for v in graf.edges[u]:
                    w = graf.edgeDist[u][v]
                    if dist[u] != math.inf and dist[u] + w < dist[v]:  
                        dist[v] = dist[u] + w
                        parent[v] = u

        # Step 3: check for negative-weight cycles. The above step  
        # guarantees shortest distances if DirectedGraph doesn't contain  
        # negative weight cycle. If we get a shorter path, then there  
        # is a cycle.  
        for u in graf.edges:  
            for v in graf.edges[u]:
                w = graf.edgeDist[u][v]
                if dist[u] != math.inf and dist[u] + w < dist[v]:  
                    # DirectedGraph contains negative weight cycle
                    return -math.inf, {}
        
        return dist, parent

    # Johnson
    # https://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-046j-design-and-analysis-of-algorithms-spring-2015/lecture-notes/MIT6_046JS15_lec11.pdf
    # https://www.geeksforgeeks.org/johnsons-algorithm/ 
    # uses Dijkstra & Bellman-Ford
    # O(V^2Log V) when we use only Dijkstra
    # O(V^2Log V + VE) when we use Bellman-Ford - for negative distances/weights
    # https://iq.opengenus.org/johnson-algorithm/
    @staticmethod
    def johnsonAPSP(graf):
        #1)Add a new vertex s to the DirectedGraph, add edges from new vertex to all vertices of G. Let the modified DirectedGraph be G’.
        newVert = 0
        graf.verts.append(newVert)
        for v in graf.verts:
            graf.addEdge(newVert, v, 0)
        #2) Run Bellman-Ford algorithm on G’ with s as source. Let the distances calculated by Bellman-Ford be h[0], h[1], .. h[V-1]
        # If we find a negative weight cycle, then return.
        # Note that the negative weight cycle cannot be created by new vertex s as there is no edge to s. All edges are from s.
        modifyDist = {}
        modifyDist, _ = DirectedGraph.bellmanFordSSSP(graf, newVert)
        
        #3) Reweight the edges of original DirectedGraph. For each edge (u, v), assign the new weight as “original weight + h[u] – h[v]”.
        altered = {}
        for u in graf.edgeDist:
            for v in graf.edgeDist[u]: 
                if graf.edgeDist[u][v]:
                    graf.edgeDist[u][v] += (modifyDist[u] - modifyDist[v])
                    if (modifyDist[u] - modifyDist[v]) != 0:
                        altered[(u,v)] = (modifyDist[u] - modifyDist[v])

        #4) Remove the added vertex s and run Dijkstra’s algorithm for every vertex.
        res = {}
        graf.removeVert(newVert)
        for src in graf.edges:
            res[src] = DirectedGraph.dijkStraHeap(graf, src)
        
        #5)Adjust final output for re-weighting
        for u, v in altered:
            res[u][0][v] -= altered[(u,v)]
            return res


    '''
    ### SPANS & CIRCUITS  ###
    '''

    '''
     Find Eulerian circuit in O(V+E) - unweighted DirectedGraph - starts & ends at save vertex, includes all verticies
     directed DirectedGraph using Hierholzer algorithm 
     - start at any vertex
     - visit, removing adjacencies
     - when a vertex has non, add to res
     - repeat until all visited
     https://www.geeksforgeeks.org/hierholzers-algorithm-directed-DirectedGraph/
     https://www.youtube.com/watch?v=8MpoO2zA2l4
    '''
    @staticmethod
    def findCircuitIter(graf, start):
        if len(graf.edges) == 0: 
            return

        res = [] 
        curr_path = [start] 
        while curr_path:
            curr_v = curr_path[-1]
            if graf.edges[curr_v]:
                next_v = graf.edges[curr_v].pop() 
                curr_path.append(next_v) 
            else: # back-track to find remaining circuit
                res.append(curr_path.pop()) 
                
        return res[::-1]
        
    #requires self.res to work
    @staticmethod
    def findCircuitRecur(graf, start, seen, res):
        if start in seen:
            return
        seen.add(start)
        for nei in self.edges[start]:
            self.findCircuitRecur(nei, seen, res)
        self.res.append(start)

    # MST Minimum Spanning Tree - subset of edges in undirected DirectedGraph w/ all vertices w/out any circuits
    # Prim's algorithm when you have a DirectedGraph with lots of edges - dense DirectedGraph
    # Note the similarity to Dijkstra
    # O(E + V log V) amortized time w/ heap
    # https://www.youtube.com/watch?v=oP2-8ysT3QQ
    # https://www.geeksforgeeks.org/prims-minimum-spanning-tree-mst-greedy-algo-5/
    # https://leetcode.com/problems/cheapest-flights-within-k-stops/discuss/359596/prims-algorithm-for-finding-minimum-spanning-treepython
    @staticmethod
    def primsMST(graf, start):
        q, seen = [], set()
        distance = defaultdict(int)
        parent = defaultdict(int)
        total = 0
        for v in graf.verts:
            parent[v] = None
            dist = 0 if v == start else math.inf
            distance[v] = dist
            heapq.heappush(q, (dist, v))
        
        while q:
            dist, v = heapq.heappop(q)
            for adjacent in graf.edgeDist[v]:
                dist = graf.edgeDist[v][adjacent]
                if dist < distance[adjacent]:
                    total += dist if distance[adjacent] >= math.inf else dist - distance[adjacent]
                    distance[adjacent] = dist
                    parent[adjacent] = v
                    heapq.heappush(q, (dist, adjacent))
        
        return parent, total #if no tgt provided, return all distances

    # O(E log V) - using union find
    # https://www.geeksforgeeks.org/kruskals-minimum-spanning-tree-algorithm-greedy-algo-2/
    @staticmethod
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
        
    @staticmethod
    def randomWalk(graf, length, soFar):
        if len(soFar) >= length:
            return soFar
        
        choices = len(graf.edges[soFar[-1]])
        j = random.randint(0, choices)
        if j == choices:
            return DirectedGraph.randomWalk(graf, length, soFar + [soFar[-1]])
        nxt = graf.edges[soFar[-1]][j]
        return DirectedGraph.randomWalk(graf, length, soFar + [nxt])
        
    '''
    ### CENTRALITY ALGORITHMS ###
    '''
    @staticmethod
    def inOutConnections(graf):
        inCnt, outCnt = defaultdict(int), defaultdict(int)
        for v in graf.edges:
            outCnt[v] += len(graf.edges[v])
            for u in graf.edges[v]:
                inCnt[u] += 1
        return (inCnt, outCnt)
    
    @staticmethod
    # Degree Centrality
    # (n-1)/SUM(d(u,v)) -- normalized inverse sum of distance to closest neighbors
    def degreeCentrality(graf, u, bNegWeights = False):
        vertCnt = len(graf.verts) - 1
        totalDist = 0
        dist, _ = DirectedGraph.bellmanFordSSSP(graf, u) if bNegWeights else DirectedGraph.dijkStraHeap(graf, u)
        for v in graf.verts:
            totalDist +=  dist[v] if dist[v] < math.inf else 0
        return vertCnt / totalDist if totalDist != 0 else math.inf
    
    @staticmethod
    # SUM(1/d(u,v))/(n-1) -- normalized sum of invertse distance to closest neighbors
    def harmonicCentrality(graf, u, bNegWeights = False):
        vertCnt = len(graf.verts) - 1
        dist, _ = DirectedGraph.bellmanFordSSSP(graf, u) if bNegWeights else DirectedGraph.dijkStraHeap(graf, u)
        totalDist = sum((1/dist[v] for v in graf.verts if dist[v]))
        return totalDist / vertCnt
        
    # Brandes algorithm - betweenness centrality - O(|V||E|)
    # counts the number of times a vertex appears in the shortest paths
    # uses slightly less efficient dijkstra version for weighted graphs
    # https://github.com/networkx/networkx/blob/master/networkx/algorithms/centrality/betweenness.py
    # BFS for non-weighted described here: http://snap.stanford.edu/class/cs224w-readings/brandes01centrality.pdf
    @staticmethod
    def brandes(graf):
        res = defaultdict(int)
        for s in graf.verts: #s == starting point for this iteration, t == target
            stack, q, seen = deque(), [], {s: 0}
            heapq.heappush(q, (0, s, s))
            parents = defaultdict(list) #shortest paths' parents s -> w
            shrtPathCnt = defaultdict(int); shrtPathCnt[s] = 1 # number of shortest paths s -> t
            dist = defaultdict(int)
            while q:
                (distance, pred, v) = heapq.heappop(q)
                if v in dist:
                    continue
                shrtPathCnt[v] += shrtPathCnt[pred]  # count paths
                stack.append(v)
                dist[v] = distance
                for w in graf.edges[v]: #iterate v's neighbors, w
                    vw_dist = distance + graf.edgeDist[v][w]
                    if w not in dist and (w not in seen or vw_dist < seen[w]):
                        seen[w] = vw_dist
                        heapq.heappush(q, (vw_dist, v, w))
                        shrtPathCnt[w] = 0.0
                        parents[w] = [v]
                    elif vw_dist == seen[w]:  # handle equal paths
                        shrtPathCnt[w] += shrtPathCnt[v]
                        parents[w].append(v)
            e = defaultdict(int)
            while stack: # S returns vertices in order of non-increasing distance from s
                w = stack.pop()
                for v in parents[w]:
                    # since v is a child of w, its count should be one greater than that of w
                    # we adjust this with "count u->w containing v / count u->w" for cases where there are more than 1 shortest path
                    e[v] += (shrtPathCnt[v]/shrtPathCnt[w]) * (1 + e[w]) 
                if w != s:
                    res[w] = res[w] + e[w]
        return res
    
    @staticmethod
    # https://www.geeksforgeeks.org/page-rank-algorithm-implementation/
    def pagerank(graf, alpha=0.85, personalization=None, max_iter=100
        , tol=1.0e-6, nstart=None, dangling=None):
        weight='weight'
        if not graf: 
            return {}

        # Creates networkx DiGraph from graf
        # https://networkx.github.io/documentation/stable/reference/classes/digraph.html
        G = nx.DiGraph()
        G.add_nodes_from([v for v in graf.verts])
        G.add_edges_from( [(u, v, {weight: graf.edgeDist[u][v]}) for u in graf.edges for v in graf.edges[u]] )
        # Create a copy in (right) stochastic form: sum of weights == 1
        W = nx.stochastic_graph(G, weight=weight) 
        N = W.number_of_nodes() 

        # Choose fixed starting vector if not given 
        if nstart is None: 
            x = dict.fromkeys(W, 1.0 / N) 
        else: 
            # Normalized nstart vector 
            s = float(sum(nstart.values())) 
            x = dict((k, v / s) for k, v in nstart.items()) 

        if personalization is None: 
            # Assign uniform personalization vector if not given 
            p = dict.fromkeys(W, 1.0 / N) 
        else: 
            missing = set(graf.verts) - set(personalization) 
            if missing: 
                raise NetworkXError('Personalization dictionary '
                                    'must have a value for every node. '
                                    'Missing nodes %s' % missing) 
            s = float(sum(personalization.values())) 
            p = dict((k, v / s) for k, v in personalization.items()) 

        if dangling is None: 
            # Use personalization vector if dangling vector not specified 
            dangling_weights = p 
        else: 
            missing = set(graf.verts) - set(dangling) 
            if missing: 
                raise NetworkXError('Dangling node dictionary '
                                    'must have a value for every node. '
                                    'Missing nodes %s' % missing) 
            s = float(sum(dangling.values())) 
            dangling_weights = dict((k, v/s) for k, v in dangling.items()) 
        dangling_nodes = [n for n in W if W.out_degree(n, weight=weight) == 0.0] 

        # power iteration: make up to max_iter iterations 
        for _ in range(max_iter): 
            xlast = x 
            x = dict.fromkeys(xlast.keys(), 0) 
            danglesum = alpha * sum(xlast[n] for n in dangling_nodes) 
            for n in x: 
                # this matrix multiply looks odd because it is 
                # doing a left multiply x^T=xlast^T*W 
                for nbr in W[n]: 
                    x[nbr] += alpha * xlast[n] * W[n][nbr][weight] 
                x[n] += danglesum * dangling_weights[n] + (1.0 - alpha) * p[n] 

            # check convergence, l1 norm 
            err = sum([abs(x[n] - xlast[n]) for n in x]) 
            if err < N*tol: 
                return x 
        raise NetworkXError('pagerank: power iteration failed to converge '
                            'in %d iterations.' % max_iter) 

        
    '''
    ### COMMUNITY ALGORITHMS ###
    '''

    @staticmethod
    # Clustering Coefficient, CC(u) = (2 * Num Triangles) / degree(u) * (degree(u) - 1)
    # global (averaged) clustering approximatation of CC --> 0->1 where 1 indicates a clique w/ all vertices connected
    # https://www.geeksforgeeks.org/clustering-coefficient-graph-theory/
    # http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.70.9248&rep=rep1&type=pd
    def average_clustering(graf, trials=1000): 
        triangles = 0
        for i in [random.randint(0, len(graf.verts) - 1) for i in range(trials)]: 
            nbrs = graf.edges[graf.verts[i]] 
            if len(nbrs) < 2: 
                continue
            u, v = random.sample(nbrs, 2) 
            if u in graf.edges[v]: 
                triangles += 1
        return triangles / float(trials) 

    # Clustering Coefficient, CC(u) = (2 * Num Triangles) / degree(u) * (degree(u) - 1)
    # https://networkx.github.io/documentation/networkx-1.10/_modules/networkx/algorithms/cluster.html
    @staticmethod
    def clustering_coefficient(graf): 
        max_weight = max( [graf.edgeDist[u][v] for u in graf.edgeDist for v in graf.edgeDist[u]] )
        nodes_nbrs= ( (n, graf.edges[n]) for n in graf.verts )
        clusterc = defaultdict(float)

        for i,nbrs in nodes_nbrs:
            i_nbrs = set(nbrs) - set([i])
            triangleCnt = 0.0
            seen = set()
            for j in i_nbrs:
                w_ij = graf.edgeDist[i][j] / max_weight
                seen.add(j)
                j_nbrs = set(graf.edges[j]) - seen # this keeps from double counting
                for k in i_nbrs & j_nbrs:
                    w_jk = graf.edgeDist[j][k] / max_weight
                    w_ki = graf.edgeDist[i][k] / max_weight
                    triangleCnt += (w_ij * w_jk * w_ki)**(1.0/3.0)
            
            if triangleCnt != 0:
                clusterc[i] = (2 * triangleCnt) / float(len(i_nbrs) * (len(i_nbrs) - 1)) # CC(u) = (2 * Num Triangles) / degree(u) * (degree(u) - 1)
            else:
                clusterc[i] = 0.0
        return clusterc
        

    @staticmethod        
    def tarjanBridges(graf):
        def __dfs(graf, u, depth):
            visitedTime[u] = depth
            
            for v in graf.edges[u]:
                if visitedTime[v] <= -math.inf:
                    __dfs(graf, v, depth + 1)
                    lowTime[u] = min(lowTime[u], lowTime[v])
                    
                    if lowTime[v] > visitedTime[u]: #it's a bridge
                        res.append([u, v])
                elif visitedTime[v] != depth - 1: #it's not the parent
                    lowTime[u] = min(lowTime[u], visitedTime[v])

        ##main
        visitedTime = [-math.inf] * len(graf.verts)
        lowTime = [math.inf] * len(graf.verts)
        
        res = []
        __dfs(graf, 0, 0)
        return res
    
    #Tarjan Articulation Points
    @staticmethod
    def tarjanAP(graf):
        def __dfs(graf, u, depth):
            visitedTime[u] = depth
            
            children = 0
            for v in graf.edges[u]:
                if visitedTime[v] <= -math.inf:
                    children += 1
                    __dfs(graf, v, depth + 1)
                    lowTime[u] = min(lowTime[u], lowTime[v])
                    
                    if depth <= 0 and children > 1: #children = non-parent neighbors, this is the midpoint of a bridge
                        res.add(u)
                    if depth > 0 and lowTime[v] >= visitedTime[u]:
                        res.add(u)
                elif visitedTime[v] != depth - 1: #it's not the parent
                    lowTime[u] = min(lowTime[u], visitedTime[v])

        ##main
        visitedTime = [-math.inf] * len(graf.verts)
        lowTime = [math.inf] * len(graf.verts)
        
        res = set()
        __dfs(graf, 0, 0)
        return res
        
    # https://www.geeksforgeeks.org/tarjan-algorithm-find-strongly-connected-components/
    @staticmethod
    def tarjanSCC(graf):
        def __dfs(graf, u, depth):
            visitedTime[u] = depth
            lowTime[u] = depth
            inStack[u] = True
            stack.append(u)
        
            for v in graf.edges[u]:
                if visitedTime[v] <= -math.inf:
                    __dfs(graf, v, depth + 1)
                    lowTime[u] = min(lowTime[u], lowTime[v])
                elif inStack[v]:
                    lowTime[u] = min(lowTime[u], visitedTime[v])
            
            # head node found, pop the stack and print an SCC 
            w = -math.inf #To store stack extracted vertices 
            if lowTime[u] == visitedTime[u]:
                tmp = []
                while w != u:
                    w = stack.pop() 
                    tmp.append(w)
                    inStack[w] = False
                res.append(tmp)

        ##main
        visitedTime = [-math.inf] * len(graf.verts)
        lowTime = [math.inf] * len(graf.verts)
        inStack = [False] * len(graf.verts)
        stack = []
        
        res = []
        for vert in graf.verts: 
            if visitedTime[vert] <= -math.inf:
                __dfs(graf, vert, 0)
        return res
    
    # https://arxiv.org/pdf/0709.2938.pdf
    # https://github.com/networkx/networkx/blob/master/networkx/algorithms/community/label_propagation.py#L97
    # https://en.wikipedia.org/wiki/Label_propagation_algorithm
    #
    # layered enhancement: https://towardsdatascience.com/layered-label-propagation-algorithm-1b181b982e80
    # outcome different each iteration.  leaving some labels blank initially can control outcome thus "semi-supervised"
    @staticmethod
    def labelPropagation(graf, lblTxt):
        labels = {n: i for i, n in enumerate(graf.verts)}
        cont = True
        while cont:
            cont = False
            nodes = list(graf.verts)
            random.shuffle(nodes)
            # Calculate the label for each node
            for node in nodes:
                if len(graf.edges[node]) < 1:
                    continue

                # Get label frequencies. Depending on the order they are processed
                # in some nodes with be in t and others in t-1, making the
                # algorithm asynchronous.
                label_freq = Counter()
                for v in graf.edgeDist[node]:
                    label_freq.update(
                        {labels[v]: graf.edgeDist[node][v]}
                    )
                # Choose the label with the highest frecuency. If more than 1 label
                # has the highest frecuency choose one randomly.
                max_freq = max(label_freq.values())
                best_labels = [
                    label for label, freq in label_freq.items() if freq == max_freq
                ]

                # Continue until all nodes have a majority label
                if labels[node] not in best_labels:
                    labels[node] = random.sample(best_labels, len(best_labels))[random.randint(0, len(best_labels)-1)]
                    cont = True

        res = defaultdict(list)
        for i in labels:
            res[lblTxt[labels[i]]].append(i)
        return res
    
    # https://github.com/taynaud/python-louvain/blob/master/community/community_louvain.py 
    # https://medium.com/walmartglobaltech/demystifying-louvains-algorithm-and-its-implementation-in-gpu-9a07cdd3b010
    # https://en.wikipedia.org/wiki/Louvain_method
    # https://towardsdatascience.com/louvain-algorithm-93fde589f58c
    @staticmethod
    def louvainModularity(graf):
        pass
        

        
    # https://www.youtube.com/watch?v=GiN3jRdgxU4  
    # https://www.geeksforgeeks.org/dinics-algorithm-maximum-flow/
    # Returns maximum flow in graph in O(VE^2)
    @staticmethod
    def dinicMaxflow(graf, s, t, rev):
        #return true if s connected to t and populate parent
        def BFS(graf, s, t): 
            nonlocal level 
            level = [-1] * len(graf.verts)
            level[s] = 0
            queue = deque([s])
               
            while queue:
                u = queue.popleft()
                
                for v in graf.edges[u]:
                    if level[v] < 0 and flow[u][v] < graf.edgeDist[u][v]:
                        queue.append(v)
                        level[v] = level[u] + 1
                        parent[v] = u
      
            return True if level[t] >= 0 else False
            
        def sendFlow(graf, u, nFlow, t, start):
            # Sink reached 
            if u == t:
                return nFlow
          
            # Traverse all adjacent edges one -by - one. 
            while start[u] < len(graf.edges[u]):
                # Pick next edge from adjacency list of u 
                e = graf.edges[u][start[u]]
                
                if level[e] == level[u] + 1 and flow[u][e] < graf.edgeDist[u][e]:
                    # find minimum flow from u to t 
                    curr_flow = min(nFlow, graf.edgeDist[u][e] - flow[u][e])
                    temp_flow = sendFlow(graf, e, curr_flow, t, start)
          
                    # flow is greater than zero 
                    if temp_flow > 0:
                        # add flow  to current edge 
                        flow[u][e] += temp_flow
          
                        # subtract flow from reverse edge 
                        # of current edge 
                        flow[e][u] -= temp_flow
                        return temp_flow
                start[u] += 1
            return 0
        
        ##start Dinci##
        if (s == t):
            return -1
      
        flow = defaultdict(dict)
        for u in graf.verts:
            for v in graf.edges[u]:
                flow[u][v] = 0
        level = [-1] * len(graf.verts)
        parent = [-1] * len(graf.verts)
        total = 0 # Initialize result 
        # Augment the flow while there is path 
        # from source to sink 
        while BFS(graf, s, t):
            # store how many edges are visited 
            start = [0] * (len(graf.verts) + 1)
      
            # while flow is not zero in graph from S to D 
            nFlow = sendFlow(graf, s, math.inf, t, start)
            while nFlow != 0:
                # Add path flow to overall flow 
                total += nFlow
                nFlow = sendFlow(graf, s, math.inf, t, start)
      
        # return maximum flow
        return total
        
    
    
        
@utility.profile       
def main():
    print('######### SORTING ##############')
    print('Topological Sort:')
    M=[[5, 2],[5, 0],[4, 0],[4, 1],[2, 3],[3, 1]]
    g = DirectedGraph([i for i in range(6)])
    for u, v in M:
        g.addEdge(u, v) 
    
    res = DirectedGraph.dfsTopologicalSort(g) 
    print('Result: ' + str(res) + ", " + str(len(res)==6)) #[5, 4, 2, 3, 1, 0])
    assert(list(res) == [5, 4, 2, 3, 1, 0])
    
    res = DirectedGraph.kahnsTopologicalSort(g) 
    print('Result: ' + str(res) + ", " + str(len(res)==6)) #[4, 5, 2, 0, 3, 1])
    assert(list(res) == [4, 5, 2, 0, 3, 1])
    


    print('######### SHORTEST PATH ##############')
    M=[[1, 2, 5],[2, 3, 2],[1, 4, 9],[1, 5, 3],[5, 6, 2],[6, 4, 2],[3, 4, 3]]
    g=DirectedGraph([i for i in range(1,7)])
    for m in M:
        g.addEdge(m[0],m[1], m[2]) 
        
    #Djikstra
    dist, path = DirectedGraph.dijkStraHeap(g, 1)
    print("\n", 'Dijkstra shortest path from 1: ' + str(dist), path, "\n")
    assert(dist[4] == 7)
    assert(path[4] == [1, 5, 6, 4])
    
    #AStar
    dist, path = DirectedGraph.aStar(g, 1, 6) 
    print('AStar shortest path from 1: ' + str(dist), path, "\n")
    assert(dist[6] == 5)
    
    #Yens
    k = 3
    dist, path = DirectedGraph.yensK(g, 1, 4, k)
    print('Yens K shortest paths from 1: ' + str(dist), path, "\n")
    assert(dist[0] == 7)
    assert(dist[1] == 9)
    assert(dist[2] == 10)
    assert(path[0] == [1, 5, 6, 4])
    assert(path[1] == [1, 4])
    assert(path[2] == [1, 2, 3, 4])
    
    #Bellman-Ford
    M=[[1, 2, 5],[2, 3, 2],[1, 4, 9],[1, 5, 3],[5, 6, 2],[6, 4, 2],[3, 4, -3]]
    g=DirectedGraph([i for i in range(1,7)])
    for m in M:
        g.addEdge(m[0],m[1], m[2])
    dist, parent = DirectedGraph.bellmanFordSSSP(g, 1)#, 4) 
    print('Bellman-Ford shortest path from 1: ' + str(dist), "\n")
    assert(dist[4] == 4)
    assert(parent[4] == 3)
    assert(parent[3] == 2)
    assert(parent[2] == 1)
    
    #Johnson APSP
    everything = DirectedGraph.johnsonAPSP(g)
    print('Johnson APSP: ' + str(everything), "\n")
    assert(everything[1][1][4] == [1, 2, 3, 4])
    assert(everything[1][0][4] == 4)

    print('######### SPANS & CIRCUITS ##############')
    #Hierholzer Eulerian Circuit
    print('Hierholzers Eulerian Circuit:')
    circuit = []
    start = 0

    g = DirectedGraph([i for i in range(3)])
    g.addEdge(0, 1)
    g.addEdge(1, 2)
    g.addEdge(2, 0)

    circuit = DirectedGraph.findCircuitIter(g, 0)
    print(circuit)

    g = DirectedGraph([i for i in range(3)])
    g.addEdge(0, 1)
    g.addEdge(0, 6)
    g.addEdge(1, 2)
    g.addEdge(2, 0)
    g.addEdge(2, 3)
    g.addEdge(3,4)
    g.addEdge(4,2)
    g.addEdge(4,5)
    g.addEdge(5,0)
    g.addEdge(6,4)

    circuit = DirectedGraph.findCircuitIter(g, 0)
    print(circuit, "\n")
    ####
    
    ##Random Walk
    print('Random Walk:')
    g=DirectedGraph([i for i in range(1,7)])
    g = DirectedGraph([i for i in range(3)])
    g.addEdge(0, 1)
    g.addEdge(0, 6)
    g.addEdge(1, 2)
    g.addEdge(2, 0)
    g.addEdge(2, 3)
    g.addEdge(3,4)
    g.addEdge(4,2)
    g.addEdge(4,5)
    g.addEdge(5,0)
    g.addEdge(6,4)
    res = DirectedGraph.randomWalk(g, 6, [2])
    print(res)

    
    print('######### CENTRALITY ##############')
    ## Degree Centrality
    print("\n Degree Centrality:")
    g = DirectedGraph([i for i in range(7)])
    M = [[0, 1], [1, 2], [2, 0], [1, 3], [1, 4], [1, 6], [3, 5], [4, 5]]
    for u, v in M:
        g.addEdge(u, v)
    inCon, outCon = DirectedGraph.inOutConnections(g)
    print(inCon, outCon)
    assert(inCon[4] == 1 and outCon[4] == 1)

    ## Closeness Centrality
    print("\n Closeness Centrality:")
    M=[[1, 2, 5],[2, 3, 2],[1, 4, 9],[1, 5, 3],[5, 6, 2],[6, 4, 2],[3, 4, -3]]
    g=DirectedGraph([i for i in range(1,7)])
    for m in M:
        g.addEdge(m[0],m[1], m[2])
    closeness = DirectedGraph.degreeCentrality(g, 1)
    print(closeness)
    assert(closeness > 0.20 and closeness < 0.21 )
    
    ## Harmonic Centrality
    print("\n Harmonic Centrality:")
    harmony = DirectedGraph.harmonicCentrality(g, 1)
    print(harmony)
    
    ## Brandes Betweeness Centrality
    M=[[1, 2, 5],[2, 3, 2],[1, 4, 9],[1, 5, 3],[5, 6, 2],[6, 4, 2],[3, 4, 3], [4, 5, 1], [4, 1, 1]]
    g=DirectedGraph([i for i in range(1,7)])
    for m in M:
        g.addEdge(m[0],m[1], m[2])
    print("\n Brandes Betweeness Centrality")
    brandes = DirectedGraph.brandes(g)
    print(brandes)
    
    ## Page Rank
    print("\n Page Rank")
    pr = DirectedGraph.pagerank(g)
    print(pr)
    
    
    print('######### COMMUNITY ##############')
    ## Clusterting Coefficient
    print("\n Clustering Coefficient:")
    cc = DirectedGraph.clustering_coefficient(g)
    print(cc)
    
    ## Approx Global Clusterting Coefficient
    print("\n Approx Global Clustering Coefficient:")
    res = DirectedGraph.average_clustering(g)
    print(res)
    
    
    ##Tarjans Bridges
    print("\n", 'Tarjans Bridges:')
    g = DirectedGraph([i for i in range(6)])
    M = [[0,1],[1,2],[2,0],[1,3],[3,4],[4,5],[5,3]]
    for u, v in M:
        g.addEdge(u, v)
    bridges = DirectedGraph.tarjanBridges(g)
    print(bridges)
    assert(bridges == [[1,3]])
    
    ##Tarjans Articulation Points
    print("\n", 'Tarjans Articulation Points:')
    g = DirectedGraph([i for i in range(6)])
    M = [[0,1],[1,2],[2,0],[1,3],[3,4],[4,5],[5,3]]
    for u, v in M:
        g.addEdge(u, v)
    
    ap = DirectedGraph.tarjanAP(g)
    list(ap).sort()
    print(ap)
    assert(ap == {1, 3})
    
    g = DirectedGraph([i for i in range(5)])
    M = [[1, 0], [0, 2], [2, 1], [0, 3], [3, 4]]
    for u, v in M:
        g.addEdge(u, v)
    ap = DirectedGraph.tarjanAP(g)
    list(ap).sort()
    print(ap)
    assert(ap == {0, 3})
    
    g = DirectedGraph([i for i in range(7)])
    M = [[0, 1], [1, 2], [2, 0], [1, 3], [1, 4], [1, 6], [3, 5], [4, 5]]
    for u, v in M:
        g.addEdge(u, v)
    
    ap = DirectedGraph.tarjanAP(g)
    list(ap).sort()
    print(ap)
    assert(ap == {1,3})
    
    ## Tarjans Strongly Connected Components
    print("\n", 'Tarjans Strongly Connected Components:')
    scc = DirectedGraph.tarjanSCC(g)
    print(scc)
    
    g = DirectedGraph([i for i in range(11)])
    M = [(0, 1), (0, 3), (1, 2), (1, 4), (2, 0), (2, 6), (3, 2), (4, 5), (4, 6), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (7, 9), (8, 9), (9, 8)]
    for u, v in M:
        g.addEdge(u, v)
    scc = DirectedGraph.tarjanSCC(g)
    print(scc)
    
    ## Label Propagation
    print("\n", 'Label Propagation:')
    g = DirectedGraph([i for i in range(11)])
    M = [(0, 1), (0, 3), (1, 2), (1, 4), (2, 0), (2, 6), (3, 2), (4, 5), (4, 6), (5, 6), (5, 7), (5, 8), (5, 9), (6, 4), (7, 9), (8, 9), (9, 8)]
    for u, v in M:
        g.addEdge(u, v)
    label = DirectedGraph.labelPropagation(g, ['red','green','blue','','brown','','orange','purple','indigo','gray','rainbow'])
    print(label)
    
    
    # Dinic's Max Flow
    print("\n", "Dinic's Max Flow:")
    g = DirectedGraph([i for i in range(7)])
    reverse = defaultdict(dict)

    g.addEdge(0, 1, 16 ) 
    reverse[0][1] = len(g.edges[1])-1
    g.addEdge(1, 0, 0) 
    reverse[1][0] = len(g.edges[0])-1

    g.addEdge(0, 2, 13 ) 
    reverse[0][2] = len(g.edges[2])-1
    g.addEdge(2, 0, 0)
    reverse[2][0] = len(g.edges[0])-1

    g.addEdge(1, 2, 10 ) 
    reverse[1][2] = len(g.edges[2])-1
    g.addEdge(2, 1, 0) 
    reverse[2][1] = len(g.edges[1])-1

    g.addEdge(1, 3, 12 ) 
    reverse[1][3] = len(g.edges[3])-1
    g.addEdge(3, 1, 0) 
    reverse[3][1] = len(g.edges[1])-1

    g.addEdge(2, 1, 4 ) 
    reverse[2][1] = len(g.edges[1])-1
    g.addEdge(1, 2, 0) 
    reverse[1][2] = len(g.edges[2])-1

    g.addEdge(2, 4, 14) 
    reverse[2][4] = len(g.edges[4])-1
    g.addEdge(4, 2, 0) 
    reverse[4][2] = len(g.edges[2])-1

    g.addEdge(3, 2, 9 ) 
    reverse[3][2] = len(g.edges[2])-1
    g.addEdge(2, 3, 0) 
    reverse[2][3] = len(g.edges[3])-1

    g.addEdge(3, 5, 20 ) 
    reverse[3][5] = len(g.edges[5])-1
    g.addEdge(5, 3, 0) 
    reverse[5][3] = len(g.edges[3])-1

    g.addEdge(4, 3, 7 ) 
    reverse[4][3] = len(g.edges[3])-1
    g.addEdge(3, 4, 0) 
    reverse[3][4] = len(g.edges[4])-1

    g.addEdge(4, 5, 4)
    reverse[4][5] = len(g.edges[5])-1
    g.addEdge(5, 4, 0)
    reverse[5][4] = len(g.edges[4])-1
    res = DirectedGraph.dinicMaxflow(g, 0, 5, reverse)
    print(res)
    assert(res == 23)
    
    
if __name__ == "__main__":
    main()

