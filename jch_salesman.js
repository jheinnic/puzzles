/** 
* The 'sequential salesman' traverses all the points in the order they are given
* in the graph. Not efficient, but easy to implement. 
*/
function JCHSalesman() {
  this.graph = {};
  this.vertex_state_by_id = { };
  this.vertex_count = 0;

  this.get_point_by_id = function get_point_by_id(point_id) {
    return this.vertex_state_by_id[point_id];
  }

  // For the sake of comparing distances, we can omit the square root because for any pair of distance
  // metrics, m and n, dist-of-m < dist-of-n, implies that dist-of-m^2 < dist-of-n^2.
  this.get_dist_squared = function(point1, point2) {
    return Math.pow(point2.x - point1.x, 2) + Math.pow(point2.y - point1.y, 2);
  }

  this.init_graph = function init_graph(graph) {
    this.graph = graph;
    var self = this;
    _(graph.points).each(function(p) {
      self.vertex_state_by_id[p.id] = {
        point: p,
        in_span_tree: 0,
        adjacent_weights: [],
        span_children: []
      };

      self.vertex_count++;
    });
    
    _(graph.arcs).each(function(a) {
      var p1 = self.get_point_by_id(a[0]);
      var p2 = self.get_point_by_id(a[1]);
      var dist_squared = self.get_dist_squared( p1, p2 );

      // TODO: Confirm a sparse hash is more efficient than a spare array.
      p1.adjacent_weights.push({ from: p1, to: p2, dist_squared: dist_squared });
      p2.adjacent_weights.push({ from: p2, to: p1, dist_squared: dist_squared });
    });
  }
  
  this.compute_plan = function(graph, start_point_id) {
    // Init
    this.init_graph(graph);
    var start_point = this.get_point_by_id(start_point_id);

    // Compute a minimal span tree
    this.compute_minimal_span_tree(start_point);

    // Perform a DFS of the span tree to derive a cycle, shortcutting around back edges as much as possible.
    // Follow all forward edges, but as an optimization, attempt to find shortcuts that avoid traversing back
    // edges.
    var retVal = this.compute_derived_cycle(start_point);
    console.debug( "Ready to return final result: " );
    console.debug(retVal);
    return retVal;
  }

  this.compute_minimal_span_tree = function compute_minimal_span_tree(start_point) {
    var candidate_edge_heap = new Heap(function(a, b) {
      return a.dist_squared - b.dist_squared;
    });

    start_point.in_span_tree = 1;
    var vertices_left = this.vertex_count - 1;
    var neighbors = start_point.adjacent_weights;
    _(neighbors).each(function(adjacency) {
      candidate_edge_heap.push(adjacency);
    });

    while(vertices_left > 0) {
      var best_new_edge = candidate_edge_heap.pop();
      while( best_new_edge.to.in_span_tree == 1 ) {
        best_new_edge = candidate_edge_heap.pop();
      }

      var next_vertex = best_new_edge.to;
      best_new_edge.from.span_children.push(next_vertex);
      next_vertex.in_span_tree = 1;
      vertices_left--;

      var neighbors = next_vertex.adjacent_weights;
      _(neighbors).each(function(adjacency) {
        if( adjacency.to.in_span_tree == 0 ) {
          candidate_edge_heap.push(adjacency);
        }
      });
    }
  }

  this.compute_derived_cycle = function(start_point) {
    var return_cycle = [start_point];
    this.derived_cycle_recursion(return_cycle, [], start_point);

    return _(return_cycle).map(function(node) {
      return node.point.id;
    });
  }

  this.derived_cycle_recursion = function derived_cycle_recursion(cycle_path, backstep_path, from_vertex) {
    backstep_path.push(from_vertex);

    var self = this;
    var children = from_vertex.span_children;
    _(children).each(function(to_vertex) {
      // Prepare a unique copy of the backstep path so its easier to prune before the next forward edge
      var backstep_path_clone = _.clone(backstep_path);
      cycle_path.push(to_vertex);

      console.debug("Travelling a forward edge to : ");
      console.debug(cycle_path);

      self.derived_cycle_recursion(cycle_path, backstep_path_clone, to_vertex);

      // TODO: Use backstep_path to bound a search for short circuits
      _(backstep_path_clone).reject(function(node) {
        _.contains(backstep_path, node)
      });
      console.debug( "Returning through: " );
      console.debug(backstep_path_clone);

      // Until TODO above, step back unconditionally.
      cycle_path.push(from_vertex);
    });
  }

  this.get_path_to_point = function(start_point, end_point) {
    
    // Breadth First Search. 
    // The 'visit_queue' consists of the current point, and a 'breadcrumb' path back to the start point.
    visit_queue = [[start_point, [start_point], 0]]
    visited = {}
    max_hits = 5;
    hits = 0;
    closest_path = null;
    closest_dist = 10000000;
    
    // We're going to BFS for the end_point.  It's not guaranteed to be the shortest path.
    // Is there a better way that is computationally fast enough?
    while(visit_queue.length > 0) {
      
      a = visit_queue.shift();
      this_point = a[0];
      this_path = a[1];
      this_dist = a[2];
      visited[this_point.id] = true
      
      if (this_point.id == end_point.id) {
        
        // We've arrived, return the breadcrumb path that took us here...
        if (this_dist < closest_dist) {
          closest_dist = this_dist
          closest_path = this_path
        }
        hits += 1;
        if (hits > max_hits) {
          break;
        }
        
      } else {
        
        // Otherwise, explore all the surrounding points...
        new_points = this.get_surrounding_points(this_point.id)
        _(new_points).each(function(p) {
          if (!visited[p.id]) {
            dist = this.get_dist(this_point, p)
            visit_queue.push([p, this_path.concat(p), this_dist + dist])
          }
        }); 
      }  
    }
    
    // Otherwise, a path doesn't exist
    if (closest_path == null)
      throw "Could not compute path from start_point to end_point! " + start_point.id + " -> " + end_point.id;
    return closest_path;
  }

  return this;
}