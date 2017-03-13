#include <iostream>
#include <vector>
#include <algorithm>
#include <queue>

using std::vector;
using std::queue;

using namespace std;


#ifdef DEBUG
const bool debug = true;
#else
const bool debug = false;
#endif


/* This class implements a bit unusual scheme for storing edges of the graph,
 * in order to retrieve the backward edge for a given edge quickly. */
class FlowGraph {

public:

  struct Edge { int from,to,capacity,flow; };

private:
  /* List of all - forward and backward - edges */
  vector<Edge> edges;

  /**
   * These adjacency lists store only indices of edges in the edges list  
   * For every vertex we store a list positions in the edge list
   */
  vector<vector<size_t> > graph;

public:

  explicit FlowGraph(size_t n): graph(n) {}
 
  void add_edge(int from, int to, int capacity) {

    /** 
     * Note that we first append a forward edge and then a Edge backward edge, 
     * so all forward edges are stored at even Edge indices (starting from 0), 
     * whereas backward edges are Edge stored at odd indices in the list edges.
     */
    Edge forward_edge = {from, to, capacity, 0};
    
    // Backward edge represents an edge in the residual graph.
    Edge backward_edge = {to, from, 0, 0};

    int edge_position = edges.size();
      
    graph[from].push_back(edge_position);
    edges.push_back(forward_edge);

    // The back edge will look like a normal edge
    // because a front edge is added just before the backedge
    // we can always find the front edge of any particular back edge
    
    graph[to].push_back(edge_position);
    edges.push_back(backward_edge);

  }

  /**
   * Run bfs on residual graph to find an augmenting path from source
   * vertex to sink vertex.
   */
  vector<size_t> find_augmenting_path(int s, int t)
  {      
    std::queue<int> q = queue<int>();
    const int max_dist = -1;

    // All vertices start out at a immense distances
    std::vector<int> dist = vector<int>(graph.size() , max_dist);

    // prev[<node>] stores the parent node in bfs exploration 
    std::vector<size_t> prev = vector<size_t>(graph.size() , -1);

    // Push source vertex into bfs queue
    q.push(s);

    // dist is distance of vertex from the source dist[s->s] == 0
    dist[s] = 0;

    prev[s] = s; // root is its own parent.
    
    while(!q.empty()) {    

      // Vertex under consideration
      int u  = q.front(); q.pop();
      
      // Get positions of every outgoing edge of this vertex in global edges list
      vector<size_t> edge_positions = graph[u];
      
      for(auto edge_position : edge_positions) {
        // doesnt like it
        Edge e =  edges[edge_position];
        
        int from = e.from;
        int to = e.to;
        
        // Edge has already been saturated and cannot be used.
        if(e.capacity - e.flow <= 0 )
          continue;

        //explore the edge endpoint [to]
        if(dist[e.to] == max_dist) {
          dist[e.to] = dist[e.from]+1;
          prev[e.to] = e.from;
          // add this end point to periphery
          q.push(e.to);
        }        
      }
    }

    // represents path to source
    vector<Edge> path;

    if(prev[t] > -1) {
      size_t cur =  t;    
      path.push_back(cur);

      while(cur < prev.size() && cur > -1  && (cur = prev[cur]) != -1) {
        path.push_back(cur);
        if(cur == s)
          break;
      }    
      
      std::reverse(path.begin(),path.end());
    }

    return path;
  }



  
  size_t size() const {
    return graph.size();
  }

  const vector<size_t>& get_ids(int from) const {
    return graph[from];
  }

  const Edge& get_edge(size_t id) const {
    return edges[id];
  }

  void add_flow(size_t id, int flow) {
    /* To get a backward edge for a true forward edge (i.e id is even), we should get id + 1
     * due to the described above scheme. On the other hand, when we have to get a "backward"
     * edge for a backward edge (i.e. get a forward edge for backward - id is odd), id - 1
     * should be taken.
     *
     * It turns out that id ^ 1 works for both cases. Think this through! */
    edges[id].flow += flow;
    edges[id ^ 1].flow -= flow;
  }

};

int max_flow(FlowGraph& graph, int source, int sink) {
  int flow = 0;

  // flow graph represents the residual network.
  vector<size_t> path = graph.find_augmenting_path(source,sink);
  // path should start with s --> t
  // find minimum edge along path
  
  return flow;
}

FlowGraph read_data() {
  int vertex_count, edge_count;
  std::cin >> vertex_count >> edge_count;

  FlowGraph graph(vertex_count);

  for (int i = 0; i < edge_count; ++i) {
    int u, v, capacity;
    std::cin >> u >> v >> capacity;
    graph.add_edge(u - 1, v - 1, capacity);
  }

  return graph;
}

int main() {
  std::ios_base::sync_with_stdio(false);
  FlowGraph graph = read_data();

  std::cout << max_flow(graph, 0, graph.size() - 1) << "\n";
  return 0;
}
