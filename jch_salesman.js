/** 
*/
function JCHSalesman( ) {
  this.graph = {};
  this.vertex_state_by_id = {};

  this.get_point_by_id = function get_point_by_id( point_id ) {
    return this.vertex_state_by_id[point_id];
  };

  // For the sake of comparing distances, we could omit the square root because for any pair of distance
  // metrics, m and n, dist-of-m < dist-of-n, implies that dist-of-m^2 < dist-of-n^2.  Unfortunately we have
  // to also deal with path distances, and so need the true distance.  Consider a single edge of distance 10
  // compared to a pair of edges that each have a distance of 6, for a total distance of 12.  The single edge
  // is a shorter path, but 10^2 = 100 and (6^2) + (6^2) = 36 + 36 = 72, and since 72 < 100, a path distance
  // calculated using the sum of distance square makes the two edge path appear shorter, when this is not in
  // fact true.
  this.get_dist = function get_dist(p1, p2) {
    return Math.sqrt(Math.pow(p2.x - p1.x, 2) + Math.pow(p2.y - p1.y, 2));
  };

  this.has_edge_between = function has_edge_between(p1, p2) {
    return _(p1.adjacent_weights).any(function(p1Adj) {
      return( p1Adj.to.point.id == p2.point.id );
    });
  };

  this.init_graph = function init_graph( graph ) {
    this.graph = graph;
    var self = this;
    _(graph.points).each(function(p) {
      self.vertex_state_by_id[p.id] = {
        point: p,
        in_span_tree: false,
        adjacent_weights: [],
        span_children: []
      };
    });
    
    _(graph.arcs).each(function( a ) {
      var p1 = self.get_point_by_id(a[0]);
      var p2 = self.get_point_by_id(a[1]);
      var dist = self.get_dist( p1.point, p2.point );

      // TODO: Confirm a sparse hash is more efficient than a spare array.
      p1.adjacent_weights.push({ from: p1, to: p2, dist: dist });
      p2.adjacent_weights.push({ from: p2, to: p1, dist: dist });
    });

    _(self.vertex_state_by_id).each( function(vertex) {
      vertex.adjacent_weights = _(vertex.adjacent_weights).sortBy('dist');
    });
  };
  
  this.compute_plan = function compute_plan( graph, start_point_id ) {
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
  };

  this.compute_minimal_span_tree = function compute_minimal_span_tree( start_point ) {
    var candidate_edge_heap = new Heap(function compare_edges(e1, e2) {
      return e1.dist - e2.dist;
    });

    // Prepare for Prim's minimum spanning tree algorithm.  Populate a binary heap with
    // adjacency information from the given root of the desired tree, start_point.
    start_point.in_span_tree = 1;
    _(start_point.adjacent_weights).each(function insert_edge(next_edge) {
      candidate_edge_heap.push(next_edge);
    });

    // Iterate once per vertex that remains in the graph.  Each iteration will select the
    // least costly edge from the binary heap that connects an unconnected vertex to the spanning tree.
    // add next adjacency to disconnected vertices that it provides, and then continue.
    _(this.graph.points.length - 1).times( function() {
      var best_new_edge = candidate_edge_heap.pop();
      while( best_new_edge.to.in_span_tree == 1 ) {
        best_new_edge = candidate_edge_heap.pop();
      }

      var next_vertex = best_new_edge.to;
      best_new_edge.from.span_children.push(next_vertex);
      next_vertex.in_span_tree = 1;

      _(next_vertex.adjacent_weights).each(function insert_edge_if_vertex_not_linked(next_edge) {
        if( next_edge.to.in_span_tree == 0 ) {
          candidate_edge_heap.push(next_edge);
        }
      });
    })
  };

  // A depth first traversal of a minimum spanning tree produces a tour.  It will not be optimal due to the
  // back edge traversal involved, but heuristics can be applied to negate much of this overhead.  This algorithm
  // may not provide a perfectly optimal result, but it should produce a good approximation in most cases.
  this.compute_derived_cycle = function compute_derived_cycle( start_point ) {
    var return_cycle = [start_point.point.id];
    var back_step_path = [];

    this.derived_cycle_recursion(return_cycle, back_step_path, start_point);

    // It's necessary to close the loop now.  Check the top of back_step_path for the identity of the last uniquely
    // visited vertex.  Use the same logic applied by
    if( back_step_path.length > 0 ) {
      this.modify_back_segment(return_cycle, back_step_path, back_step_path[0], start_point);
    } else {
      return_cycle.push( start_point.point.id );
    }

    return return_cycle;
  };

  this.derived_cycle_recursion = function derived_cycle_recursion( cycle_path, back_step_path, from_vertex ) {
    var self = this;
    console.debug( "Recursive traversal call on having appended a forward edge to vertex " + from_vertex.point.id + ":" );

    var children = from_vertex.span_children;

    // Do not step back to the from_vertex as recursion unwinds.  Instead, rely on logic that precedes each
    // subsequent forward step and applies a heuristic to optimize unnecessary back-steps into shorter paths.
    // The best optimization is a direct adjacency from the first vertex the tree traversal back-steps from that
    // lands where the next forward edge traversal will be heading.  The next best optimization is a shortest
    // path through other nodes that still has an overall cost less than the original back-stepping path.  If
    // neither exists, we have to use the back-stepping path from the minimum spanning tree traversal as-is.
    if( children.length >= 1 ) {
      // The first child never requires handling back-stepped paths as its recursive call is the first.
      var first_child = _(children).first();
      cycle_path.push(first_child.point.id);

      back_step_path.push(from_vertex);
      self.derived_cycle_recursion(cycle_path, back_step_path, first_child);

      _.chain(children).rest().each(function(to_vertex) {
        // Get a path that accounts for any back-stepping from the previous child and
        // visit the next one (to_vertex).
        self.modify_back_segment(cycle_path, back_step_path, from_vertex, to_vertex);

        // Prepare to recursively call for the next child
        back_step_path.push(from_vertex);
        self.derived_cycle_recursion(cycle_path, back_step_path, to_vertex);
      });
    } else {
      back_step_path.push(from_vertex);
    }
  };

  this.get_path_between = function get_path_between( start_point, end_point, worst_case_cost ) {
    var self = this;
    var search_context = new SearchContext(end_point, worst_case_cost);
    search_context.mark_in_use(start_point);

    // Depth First Search to build a map from vertex to the best edge to depart from it, if any,
    // to find a shortest path to our end goal vertex.
    _(start_point.adjacent_weights).each(function( next_edge ) {
      if( next_edge.to.point.id == search_context.end_vertex_id ) {
        console.log("...and found immediate adjacency with " + search_context.end_vertex_id);
        return( [search_context.end_vertex_id] );
      }

      search_context.visited[next_edge.to.point.id] =
        new VertexContext( next_edge, next_edge.dist );
      self.recursive_get_best_path( next_edge, next_edge.dist, search_context );
    });
    search_context.clear_in_use(start_point);

    // Reconstruct a minimal path from start to end by following the path through edges chosen
    // during first step, tracing from end_point backwards towards start_point.  For each edge,
    // record the node travels to.  When all edges are examined, reverse the list for a path that
    // begins with the first node travelled to from start_point and ends at end_point itself.
    var next_vertex_id = end_point.point.id;
    var returnPath = [];
    while( next_vertex_id != start_point.point.id ) {
      var next_edge = search_context.visited[next_vertex_id].best_edge;
      next_vertex_id = next_edge.from.point.id;
      returnPath.push(next_edge.to.point.id);
    }
    returnPath.reverse();

    console.log("...and found this shortest connecting path:");
    console.debug(returnPath);
    return returnPath;
  };

  // TODO: Replace first two arguments with a VertextContext object.  It encapsulates both parameters.
  this.recursive_get_best_path = function recursive_get_best_path( current_edge_in, current_dist, search_context ) {
    search_context.mark_in_use(current_edge_in.to);

    var self = this;
    _(current_edge_in.to.adjacent_weights).any( function( next_edge_out ) {
      // Skip past any vertices already in use deeper down the call stack without aborting the search.
      if( search_context.is_in_use(next_edge_out.to) ) { return false; }

      // Vertices are sorted in from least to most distant.  Abort the search here if its distance would put us in
      // range of paths that exceed the maximum distance threshold.
      var next_dist = current_dist + next_edge_out.dist;
      if( next_dist > search_context.max_dist ) { return true; }

      var vertex_context = search_context.visited[next_edge_out.to.point.id];
      if( _.isUndefined(vertex_context) || next_dist < vertex_context.get_max_dist() ) {
        vertex_context = new VertexContext(next_edge_out, next_dist);
        search_context.visited[next_edge_out.to.point.id] = vertex_context;
      }

      if( next_edge_out.to.point.id == search_context.end_vertex_id ) {
        // There is a new maximum threshold for best cost.
        // There will be no traversal into this node--its terminal.
        search_context.set_max_dist(next_dist);
      } else {
        self.recursive_get_best_path(next_edge_out, next_dist, search_context);
      }
    });

    search_context.clear_in_use(current_edge_in.to);

    // Return false so that any() keeps looking.
    return false;
  };
    
  this.modify_back_segment = function(cycle_path, back_step_stack, last_back_step_vertex, next_forward_vertex) {
    // Before advancing a forward edge, check whether we need to account for back_steps from the spanning
    // tree's depth first traversal.  If we have had to step back, let the path from the deepest ancestor
    // to this call stack frame's last_back-step_vertex, to this call stack frame's for loop's upcoming next_forward_vertex
    // represent a worst-case boundary and search for a
    var origin = back_step_stack.pop();
    if( origin != last_back_step_vertex ) {
      var current = origin;
      var worst_case_path = [];
      var worst_case_cost = 0;

      while( current != last_back_step_vertex ) {
        var next = back_step_stack.pop( );

        // Leverage Euclidean and undirected symmetries.  Weight(current->next) == Weight(next->current)
        // TODO: Refactor later to track the tree structure using Adjacency objects so we need not recalculate the
        //       distance squared cost factors here.
        worst_case_cost += this.get_dist(current.point, next.point);

        // Track the path back as we measure it so we know what it is if we find no shorter path from
        // the ancestor from which we made the first unaccounted back_step to the upcoming forward next_forward_vertex
        worst_case_path.push(next.point.id);

        // Advance the iteration, working back towards last_back-step_vertex.  The back_step path is populated by
        // appending to the right, so the partial reverse path is inferred by popping elements off the
        // right hand array end.
        current = next;
      }

      // Be sure to include the extra step from last_back-step_vertex to next_forward_vertex, otherwise the search for
      // a better shortest path may be under-state its cost tolerance and fail to find when it should find just fine.
      worst_case_path.push(next_forward_vertex.point.id);
      worst_case_cost += this.get_dist(current.point, next_forward_vertex.point);
      console.debug(
        "Optimizing a backward traversal path from " + origin.point.id +
        " to " + next_forward_vertex.point.id + " with maximum cost " + worst_case_cost +
        " for partial back edge path: ");
      console.debug(worst_case_path);

      // The best case scenario would be a direct edge from origin to next_forward_vertex.  The shortest distance
      // between any two points in a Euclidean plane is a straight line.  There may not be a direct adjacency, but
      // there may still be a shorter path from back_step origin to the next next_forward_vertex
      // other than the worst-case-scenario of reversing the original path from last_back-step_vertex to back_step
      // origin.
      if(this.has_edge_between(origin, next_forward_vertex) == false) {
        console.log(
          "No direct adjacency from " + origin.point.id + " to " +
          next_forward_vertex.point.id + " exists.  Verifying we have the best indirect path..."
        );
        _(this.get_path_between(origin, next_forward_vertex, worst_case_cost)).each(function(path_vertex_id) {
          cycle_path.push(path_vertex_id);
        });
      } else {
        console.log("Using direct adjacency from " + origin.point.id + " to " + next_forward_vertex.point.id + "." );
        cycle_path.push(next_forward_vertex.point.id);
      }
    }
  };

  return this;
};

function SearchContext(end_vertex, worst_case_cost) {
  this.visited = { };
  this.max_dist = worst_case_cost + 1;
  this.end_vertex_id = end_vertex.point.id;

  this.set_max_dist = function set_max_dist(new_max_dist) {
    this.max_dist = new_max_dist;
  };

  this.mark_in_use = function mark_in_use(p1) {
    p1.in_use = 1;
  }

  this.clear_in_use = function clear_in_use(p1) {
    p1.in_use = 0;
  }

  this.is_in_use = function is_in_use(p1) {
    p1.in_use == 1;
  }

return this;
}

function VertexContext( best_edge, max_dist ) {
  this.best_edge = best_edge;
  this.max_dist = max_dist;
  // this.point = p,
  this.in_span_tree = false,
  this.adjacent_weights = [],
  this.span_children = []

  this.set_max_dist = function set_max_dist(new_dist) {
    this.max_dist = new_dist;
  };

  this.get_max_dist = function get_max_dist() {
    return this.max_dist;
  };

  return this;
}
