#include <algorithm>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <utility>
#include <vector>

using std::vector;
using std::cin;
using std::cout;
using std::pair;
using std::map;
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

    if(debug)
      std::cerr<<"edge:["<<from<<"->"<<to<<"] capacity "<<capacity<<endl;
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
    const int undefined = -1;

    // All vertices start out at a immense distances
    std::vector<int> dist = vector<int>(graph.size() , undefined);

    // prev[<node>] stores the parent node in bfs exploration
    std::vector<size_t> prev = vector<size_t>(graph.size() , undefined);
    
    vector<size_t> path_edges = vector<size_t> (edges.size(), undefined);
    
    // Push source vertex into bfs queue
    q.push(s);

    // dist is distance of vertex from the source dist[s->s] == 0
    dist[s] = 0;

    prev[s] = s; // root is its own parent.

    while(!q.empty()) {

      // Vertex under consideration
      int u  = q.front(); q.pop();

      if(debug)
        std::fprintf(stderr,"bfs vertex[%d]\n",u);

      // Get positions of every outgoing edge of
      // this vertex in global edges list
      vector<size_t> edge_positions = graph[u];

      for(auto edge_position : edge_positions) {
        
        for(int i = 0 ; i < 2; i++ ) { 
          //Edge e = i == 0 ? edges[edge_position] : edges[edge_position + 1];
          if( i > 0)
            edge_position++;
          Edge e = edges[edge_position];
          int from = e.from;
          int to = e.to;

          // Edge has already been saturated and cannot be used.
          if(e.capacity - e.flow <= 0 )
            continue;

          //explore the edge endpoint [to]
          if(dist[e.to] == undefined) {
            dist[e.to] = dist[e.from]+1;
            prev[e.to] = e.from;
            path_edges[e.to] = edge_position; // store the edge where entered this vertex from
            // add this end point to periphery
            q.push(e.to);
          }
          
        }
      }
    }

    // represents path to source
    vector<size_t> retval;
    vector<size_t> path;

    if(debug) {
      if(debug)
        std::cerr<<"t:"<<t<<endl;
      if(debug)
        std::cerr<<"prev:[0-"<<prev.size()<<")"<<endl;
      int i = 0;
      for(auto p : prev){
        if(debug)
          std::cerr<<i++<<" "<<(int)p<<endl;
      }
      if(debug)
        std::cerr<<" sink prev: "<<prev[t]<<endl;
      if(debug)
        std::cerr<<"s:"<<s<<endl;
    }

    if(((int)prev[t]) > -1) {
      size_t cur =  t;
      
      path.push_back(cur);
      if(debug)
        std::cerr<<"pushing "<<cur<<endl;
      

      while(cur < prev.size() && ((int)cur > -1)  && ((int)(cur = prev[cur])) != -1) {
        path.push_back(cur);
        if(debug)
          std::cerr<<"pushing "<<cur<<endl;
        
        if(cur == s)
          break;
      }
      
      std::reverse(path.begin(),path.end());

      for(auto v : path){
        if(debug)
          std::cerr<<v<<" ";
      }
      if(debug)
        std::cerr<<endl;     
    }

    if(debug)
      std::cerr<<"path size["<<path.size()<<"]"<<endl;

    for(int i = 0 ; i < (int)(path.size()-1); i++){
      if(debug)
        std::cerr<<"i "<<i<<" path "<<path.size()<<endl;
      
      size_t cur = path[i];
      size_t next = path[i+1];
      
      if(debug)
        std::cerr<<"next:"<<next<<endl;
      
      size_t edge_id = path_edges[next];
      retval.push_back(edge_id);
    }
    
    return retval;
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


  int max_flow(int source, int sink) {
    
    int flow = 0;

    // flow graph represents the residual network.
    while(true) {
    
      vector<size_t> path = this->find_augmenting_path(source,sink);

      // till we can't an augmenting path
      if(path.size() <= 0) { 
        if(debug)
          std::cerr<<"Could not find any more paths!"<<std::endl;
        break;
      }

      // find maximum flow we can add based on minimum flow we can add
      FlowGraph::Edge first_edge = this->get_edge(path[0]);
      int min_flow = first_edge.capacity - first_edge.flow ;

      for(auto edge_id : path) {
        FlowGraph::Edge edge = this->get_edge(edge_id);
        int cur_flow = edge.capacity - edge.flow;
        if( cur_flow <  min_flow) {
          min_flow = cur_flow;
        }
      }

      for(auto edge_id : path) {
        if(debug)
          std::cerr<<"Adding flow :"<<min_flow<<endl;
        this->add_flow(edge_id,min_flow);
      }
    
    }//end while. flow has bn constructed.

    vector<size_t> edge_positions = this->get_ids(source);
    
    for(int edge_position : edge_positions) {
      flow += this->get_edge(edge_position).flow;
    }
    
    return flow;
  }

  void print_edges() {
    for(auto e: edges) {
      if(debug)
        std::cerr<<"("<<e.from<<"->"<<e.to<<")"<<"->"<<"["<<e.flow<<"/"<<e.capacity<<"]"<<endl;
    }
  }
  
  std::vector<std::pair<int,int>> bipartite_matching(int source,int sink,pair<int,int> & first_partition,pair<int,int> & second_partition) {
    
    if(debug) { 
      std::cerr<<"==================================="<<endl;
      std::cerr<<"source : "<<source<<" sink : "<<sink<<endl;
      std::cerr<<"==================================="<<endl;
      print_edges();
      std::cerr<<"==================================="<<endl;
    }

    vector<pair<int,int>> matching; 
    for(auto e: edges) {      
      if(e.flow && e.from != source && e.to != sink &&
         e.from >= first_partition.first && e.from <= first_partition.second
         && e.to >= second_partition.first && e.to <= second_partition.second
         ) {
        matching.push_back(pair<int,int>(e.from,e.to));
      }      
    }

    return matching;
  }

  
};


class MaxMatching {
 public:
  void Solve() {
    vector<vector<bool>> adj_matrix = ReadData();
    vector<int> matching = FindMatching(adj_matrix);
    WriteResponse(matching);
  }

 private:
  
  /**
   * Reads in matrix of bit values representing the adjacency matrix 
   * of input values.
   */
  vector<vector<bool>> ReadData() {
    
    int num_left, num_right;
    cin >> num_left >> num_right;
    
    vector<vector<bool>> adj_matrix(num_left, vector<bool>(num_right));
    
    for (int i = 0; i < num_left; ++i)
      for (int j = 0; j < num_right; ++j) {
        int bit;
        cin >> bit;
        adj_matrix[i][j] = (bit == 1);
      }
    // The source vertex is connected to every element 
    return adj_matrix;
  }

  void WriteResponse(const vector<int>& matching) {
    for (int i = 0; i < matching.size(); ++i) {
      if (i > 0)
        cout << " ";
      if (matching[i] == -1)
        cout << "-1";
      else
        cout << (matching[i] + 1);
    }
    cout << "\n";
  }

  vector<int> FindMatching(const vector<vector<bool>>& adj_matrix) {
    // num_rows: number of rows we use to match
    int num_rows = adj_matrix.size();
    
    // num_columns: number of columns used.
    int num_columns = adj_matrix[0].size();

    // Assumes num_rows < num_columns , which seems true in
    // our case
    vector<int> matching(num_rows, -1);

#define first_partition(i) (1+i)
#define second_partition(j)   (1+num_rows+j)
    
    // we reserve two nodes for source and sink
    FlowGraph fg(num_rows+num_columns+2);
    
    // source node is connected to every node in the row'th numbered node
    // row numbers start from 1 to num_rows  [1,num_rows]
    int source = 0;
    for(int i = 0  ; i < num_rows ; i++)
      fg.add_edge(source,first_partition(i),1);

    /**
     * adj_matrix[i][j] represents if (i,j) is an edge 
     */
    for(int i = 0; i < num_rows; i++) {
      for(int j  = 0; j < num_columns;j++) {
        if(adj_matrix[i][j]) {
          fg.add_edge(first_partition(i), second_partition(j) ,1);
        }
      }
    }
    
    int sink = 1+num_rows+num_columns;
    for(int i = 0; i < num_columns;i++)
      fg.add_edge(second_partition(i),sink,1);

  
    if(debug) {
      std::cerr<<"--------------------------------------------------"<<endl; 
      std::cerr<<"Before Computing Flow "<<endl; 
      std::cerr<<"--------------------------------------------------"<<endl; 
      fg.print_edges();
      std::cerr<<"--------------------------------------------------"<<endl; 
    }
    
    int max_flow = fg.max_flow(source,sink);
    if(debug)
      std::cerr<<"Found max flow "<<max_flow<<endl;
    
    if(debug) {
      std::cerr<<"--------------------------------------------------"<<endl; 
      std::cerr<<"After Computing Flow "<<endl; 
      std::cerr<<"--------------------------------------------------"<<endl; 
      fg.print_edges();
      std::cerr<<"--------------------------------------------------"<<endl; 
    }
    pair<int,int> first(1,num_rows+1);
    pair<int,int> second(num_rows+1,num_rows+num_columns+1);
    auto matched_pairs = fg.bipartite_matching(source,sink,first,second);

    for(auto match : matched_pairs) {
      
      if(debug) {
        std::cerr<<match.first<<"=>"<<match.second<<" ";
        std::cerr<<match.first-1<<"->"<<match.second - num_rows -1  <<std::endl;
      }

      int a = match.first - 1 ;
      int b = match.second - num_rows -1 ;

      matching[a] = b;
    }
    return matching;
  }
};

int main() {
  std::ios_base::sync_with_stdio(false);
  MaxMatching max_matching;
  max_matching.Solve();
  return 0;
}
