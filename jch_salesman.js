/** 
*/
function JCHSalesman( ) {
  this.graph = {};
  this.vertex_context_by_id = {};

  this.get_vertex_by_id = function get_vertex_by_id(id) {
    return this.vertex_context_by_id[id];
  };

  // For the sake of comparing distances, we could omit the square root because for any pair of distance
  // metrics, m and n, dist-of-m < dist-of-n, implies that dist-of-m^2 < dist-of-n^2.  Unfortunately we have
  // to also deal with path distances, and so need the true distance.  Consider a single edge of distance 10
  // compared to a pair of edges that each have a distance of 6, for a total distance of 12.  The single edge
  // is a shorter path, but 10^2 = 100 and (6^2) + (6^2) = 36 + 36 = 72, and since 72 < 100, a path distance
  // calculated using the sum of distance square makes the two edge path appear shorter, when this is not in
  // fact true.
  function get_distance(p1, p2) {
    return Math.sqrt(Math.pow(p2.get_x() - p1.get_x(), 2) + Math.pow(p2.get_y() - p1.get_y(), 2));
  };

  this.init_graph = function init_graph( graph ) {
    var self = this;

    // Transform each graph point into an object augmented for this analysis.
    this.graph = graph;
    this.vertex_context_by_id =
      _.object(
        _(graph.points).map(function(p) { return [p.id, new VertexContext(p)]; })
      );

    // Populate each VertexContext's list of neighboring EdgeContext metadata.
    _(graph.arcs).each(function( a ) {
      var p1 = self.get_vertex_by_id(a[0]);
      var p2 = self.get_vertex_by_id(a[1]);

      p1.add_neighbor_edge(p2, get_distance(p1, p2));
    });

    // Sort the edge lists by increasing distance order to enable faster dead-end pruning when searching
    // for minimum distance paths between known vertex pairs.
    _(this.vertex_context_by_id).each(function(vertex_context) {
      vertex_context.sort_neighbor_edges();
    });
  };

  this.compute_plan = function compute_plan( graph, start_vertex_id ) {
    // Init graph structures
    this.init_graph(graph);
    var start_point = this.get_vertex_by_id(start_vertex_id);

    // Compute a minimal span tree
    this.compute_minimal_span_tree(start_point);

    // Perform a DFS of the span tree to derive a cycle, shortcutting around back edges as much as possible.
    // Follow all forward edges, but as an optimization, attempt to find shortcuts that avoid traversing back
    // edges.
    return this.compute_derived_cycle(start_point);
  };

  this.compute_minimal_span_tree = function compute_minimal_span_tree( start_point ) {
    var candidate_edge_heap = new Heap(function compare_edges(e1, e2) {
      return e1.get_distance() - e2.get_distance();
    });

    // Prepare for Prim's minimum spanning tree algorithm.  Populate a binary heap with
    // adjacency information from the given root of the desired tree, start_point.
    start_point.mark_min_span_tree_root(candidate_edge_heap);

    // Iterate once per vertex of the graph, excluding the MST root already handled.  During each
    // iteration, select the least costly edge that points toward a vertex not yet connected to
    // the spanning tree.  Add the chosen edge to the tree.  Then insert to the priority queue
    // for next added edges every outbound edge that runs from the newly-linked vertex to a vertex
    // not yet connected to the spanning tree.
    _(this.graph.points.length - 1).times( function() {
      var best_new_edge = candidate_edge_heap.pop();
      while( best_new_edge.get_to().is_in_min_span_tree() ) {
        best_new_edge = candidate_edge_heap.pop();
      }

      best_new_edge.add_to_min_span_tree(candidate_edge_heap);
    })
  };

  // A depth first traversal of a Eulerized minimum spanning tree produces a tour.  It will not be optimal due to
  // back edge traversal, but heuristics can optimize around this overhead.  This algorithm strives for a good
  // approximation and does not guarantee a perfectly optimal result.
  this.compute_derived_cycle = function compute_derived_cycle( start_point ) {
    var return_cycle = [start_point.get_id()];
    var back_step_stack = [];

    console.group();
    this.derived_cycle_recursion(return_cycle, back_step_stack, start_point);
    console.debug(return_cycle);
    console.groupEnd();
    console.group();

    // It's necessary to close the loop now.  Check the top of back_step_stack for the identity of the last uniquely
    // visited vertex.  Use the same logic applied by
    if( back_step_stack.length > 1 ) {
      var initial_frame = back_step_stack[back_step_stack.length - 1];
      var worst_case_distance =
        back_step_stack.reduce( function(distance, frame) {
          return distance + frame.get_distance();
        }, 0
      );

      console.debug(
        "Calculating a final return path home from " + initial_frame.get_to_id() +
        " with a maximum distance of " + worst_case_distance + "..."
      );
      var return_path = new MinDistancePathSearch(initial_frame.get_to(), start_point, worst_case_distance);
      _(return_path.get_result()).each(function(path_vertex_id) {
        return_cycle.push(path_vertex_id);
      });
    } else {
      return_cycle.push( start_point.get_id() );
      console.debug("Returning from a state that coincidentally requires no back-step edges to return home.");
    }

    console.debug("Final computed cycle is:");
    console.debug(return_cycle);
    console.groupEnd();

    return return_cycle;
  };

  this.derived_cycle_recursion = function derived_cycle_recursion( cycle_path, back_step_stack, from_vertex ) {
    var self = this;
    console.debug("Recursion for forward edge to " + from_vertex.get_id() + ":");

    var children = from_vertex.span_children;

    // Do not step back to the from_vertex as recursion unwinds.  Instead, rely on logic that precedes each
    // subsequent forward step and applies a heuristic to optimize unnecessary back-steps into shorter paths.
    // The best optimization is a direct adjacency from the first vertex the tree traversal back-steps from that
    // lands where the next forward edge traversal will be heading.  The next best optimization is a shortest
    // path through other nodes that still has an overall cost less than the original back-stepping path.  If
    // neither exists, we have to use the back-stepping path from the minimum spanning tree traversal as-is.
    if( children.length >= 1 ) {
      // The first child never requires handling back-stepped paths as its recursive call is the first.
      var first_child_edge = _(children).first();
      cycle_path.push(first_child_edge.get_to_id());
      back_step_stack.push(first_child_edge);
      self.derived_cycle_recursion(cycle_path, back_step_stack, first_child_edge.get_to());

      // Subsequent children
      _.chain(children).rest().each(function(next_child_edge) {
        // Get a path that accounts for any back-stepping from the previous child and
        // visit the next one (to_vertex).
        self.modify_back_segment(cycle_path, back_step_stack, from_vertex, next_child_edge);
        back_step_stack.push(next_child_edge);
        self.derived_cycle_recursion(cycle_path, back_step_stack, next_child_edge.get_to());
      });
    }
  };

  this.modify_back_segment = function modify_back_segment(cycle_path, back_step_stack, last_back_step_to, forward_edge) {
    // Close out the preceding run of recursive appends.
    console.debug(cycle_path);
    console.groupEnd();

    // Before advancing a forward edge, check whether we need to account for back_steps from the spanning
    // tree's depth first traversal.  If we have had to step back, let the path from the deepest ancestor
    // to this call stack frame's last_back-step_vertex, to this call stack frame's for loop's upcoming
    // to_vertex represent a worst-case boundary and search for a
    var origin = back_step_stack[back_step_stack.length - 1];
    var worst_case_path = [];
    var worst_case_dist = 0;
    var current;

    do {
      // Rewind current to the edge for the previous stack frame.  If the previous stack frame is the one we
      // are returning to, it will be left on the stack and this loop will terminate.
      current = back_step_stack.pop( );

      // In order to define an upper bound for path distance the search for an optimal path segment should
      // consider, before pruning traversal paths, calculate the distance of the path used to backtrace through
      // a search of the original minimum distance spanning tree.
      worst_case_dist += current.get_distance();

      // Track the path back as we measure it so we can report on it in debug messages.
      worst_case_path.push(current.get_from_id());
    } while( current.get_from() != last_back_step_to );

    // In addition to the path element through unwinding stack frames, we need to append a path element for the
    // next forward step.  That extra destination is necessary to define the optimization scope--we're looking for
    // a better alternative to N back steps and one forward step.
    worst_case_path.push(forward_edge.get_to_id());
    worst_case_dist += forward_edge.get_distance();

    // Wrap a group around the debug information for the back-step path and its consolidation.
    console.group();
    console.debug(
      "Optimizing back-step path from " + origin.get_to_id() +
      " to " + forward_edge.get_to_id() +
      " with distance of " + worst_case_dist + " units and initial content:" );
    console.debug(worst_case_path);

    // The best case scenario would be a direct edge from origin to to_vertex.  The shortest distance
    // between any two points in a Euclidean plane is a straight line.  There may not be a direct adjacency,
    // but there may still be a shorter path from back_step origin to the next to_vertex  other than the
    // worst-case-scenario of reversing the original path from last_back-step_vertex to back_step origin.
    var search_context = new MinDistancePathSearch(origin.get_to(), forward_edge.get_to(), worst_case_dist);
    _(search_context.get_result()).each(function(path_vertex_id) {
      cycle_path.push(path_vertex_id);
    });

    console.debug( "...such that the cycle being computed has now grown to:" );
    console.debug(cycle_path);
    console.groupEnd();
    console.group();
  };

  return this;
};

function MinDistancePathSearch(start_vertex, end_vertex, worst_case_dist) {
  this.start_vertex = start_vertex;
  this.end_vertex_id = end_vertex.get_id();
  this.best_path_dist = _.object([start_vertex.get_id()], [-1]);
  this.best_incoming_edge = { };
  this.max_dist = worst_case_dist + 1;

  var self = this;

  // Return code constants.  A poor man's enum.
  const PATH_EXCEEDS_MAX_DIST = -1;
  const PATH_WOULD_HAVE_CYCLE = -2;
  const SHORTER_PATH_ALREADY_FOUND = -3;

  // Let e1 be an edge from p1 to p2.  Let p1_dist be the current search path distance to p1.
  // Return PATH_EXCEEDS_MAX_DIST if e1 would make the path too long to be worth considering.
  // Return PATH_WOULD_HAVE_CYCLE if p2 is already being examined from an earlier call frame.
  // Return SHORTER_PATH_ALREADY_FOUND if there is already a known path to p2 with a shorter length.
  // Return the sum of p1_dist and e1.get_distance() if a recursion to e1 is required.
  function test_for_edge_recursion(e1, p1_distance) {
    var p2_id = e1.get_to_id();
    var p2_state;

    if( _.isUndefined(self.best_path_dist[p2_id]) ) {
      p2_state = self.max_dist + 1;
      self.best_path_dist[p2_id] = p2_state;
    } else {
      p2_state = self.best_path_dist[p2_id];
      if( p2_state < 0 ) {
        return PATH_WOULD_HAVE_CYCLE;
      }
    }

    var next_distance = p1_distance + e1.get_distance();
    if( next_distance > self.max_dist ) {
      return PATH_EXCEEDS_MAX_DIST;
    } else if( next_distance > p2_state ) {
      return SHORTER_PATH_ALREADY_FOUND;
    } else if( p2_id != self.end_vertex_id ) {
      // Recursion will be required.
      self.best_path_dist[p2_id] = -1 * next_distance;
    } else {
      // Recursion will not be required.
      self.best_path_dist[p2_id] = next_distance;
    }

    self.best_incoming_edge[p2_id] = e1;
    return next_distance;
  }

  this.recursive_get_best_path = function recursive_get_best_path( current_edge_in, current_dist ) {
    var self = this;
    var p2 = current_edge_in.get_to();
    p2.each_neighbor_until( function process_child_edge(next_edge_out) {
      var distance_or_error = test_for_edge_recursion(next_edge_out, current_dist);
      if( distance_or_error < 0 ) {
        switch(distance_or_error) {
          case PATH_EXCEEDS_MAX_DIST:
            // Since edges are in sorted order, there is no point in traversing further.
            return true;
          case PATH_WOULD_HAVE_CYCLE:
            // Skip past any vertices already in use deeper down the call stack that would create a cycle
            return false;
          case SHORTER_PATH_ALREADY_FOUND:
            // Skip any edges where there is nothing new we can find out by further recursion.
            return false;
          default:
            throw "Invalid error code";
        }
      }

      if( next_edge_out.get_to_id() == self.end_vertex_id ) {
        // The distance to goal along the current search path is the new threshold for any future
        // minimal path candidates.  There is no need to add another recursive call--we've reached
        // the goal vertex and identified a new local minimum distance.
        self.max_dist = distance_or_error;
      } else {
        self.recursive_get_best_path(next_edge_out, distance_or_error);
      }

      // Return false so we continue iterating
      return false;
    });

    // Change the best_distance flag for the vertex whose call stack is about to end to indicate it
    // can once be appended to a future search path without creating a cycle if reached again from an
    // alternate future search path.
    this.best_path_dist[p2.get_id()] *= -1;
  };

  // Depth First Search to build a map from vertex to the best edge to depart from it, if any,
  // to find a shortest path to our end goal vertex.
  start_vertex.each_neighbor_until(function begin_dfs( next_edge ) {
    var retVal;
    var distance_or_error = test_for_edge_recursion( next_edge, 0 );

    if( distance_or_error == PATH_EXCEEDS_MAX_DIST ) {
      // Since edges are in sorted order, there is no point in examining subsequent children--the result
      // will always be the same.
      retVal = true;
    } else if( next_edge.get_to_id() == self.end_vertex_id ) {
      // The only case where we can stop immediately on finding the terminal vertex is when it is
      // directly adjacent to the starting vertex.  In all other cases there may be a shorter path
      // that just happened to have a longer vertex early enough to place it late in the search order.
      // Direct adjacency may likewise not get discovered first, but no better solution exists by
      // virtue of the triangle inequality constraint on Euclidean space.
      self.best_incoming_edge[self.end_vertex_id] = next_edge;
      self.best_path_dist[self.end_vertex_id] = next_edge.get_distance();
      self.max_dist = next_edge.get_distance();
      retVal = true;
    } else {
      // Make a recursive call for the next child, then return false to iterate to the next adjacency.
      self.recursive_get_best_path(next_edge, distance_or_error);
      retVal = false;
    }

    return retVal;
  });

  // Reconstruct the minimal path by tracing the edges selected in the loop above from end_vertex
  // backwards towards start_vertex.  After all edges have been traced, reverse the list to get
  // the path's vertices in the right order.
  //
  // This implementation is not considering the possibility that no path is found because we only
  // use this search to optimize a path of back-edges in a minimum spanning tree embedded in the
  // original graph.  In the degenerate case, we will at least find the same path of back edges.

  this.get_result = function get_result() {
    var return_path = [];

    var next_vertex_id = this.end_vertex_id;
    var start_vertex_id = this.start_vertex.get_id();
    while( next_vertex_id != start_vertex_id ) {
      var next_edge = this.best_incoming_edge[next_vertex_id];
      next_vertex_id = next_edge.get_from_id();
      return_path.push(next_edge.get_to_id());
    }

    return_path.reverse();
    console.debug("...and found this path with a minimum distance of " + this.max_dist + ":");
    console.debug(return_path);
    return return_path;
  };

  return this;
}

//
//  Vertex model for Prim's minimum spanning tree algorithm
function VertexContext( p ) {
  // Invariant graph spatial information.
  this.id = p.id;
  this.x = p.x;
  this.y = p.y;
  this.neighbor_edges = [];

  // Vertex state for Prim's minimum spanning tree calculation.

  // When span_parent is null, a vertex is not yet linked to the minimum spanning tree.  When set,
  // it is either pointing up the tree to a true parent or to itself.  In the latter case, the vertex
  // is root of the minimum spanning tree.
  this.span_parent = null;

  // span_children is the subset of all edges (from neighbor_edges) that are define the discovered
  // minimum spanning tree.
  this.span_children = [];

  this.mark_min_span_tree_root = function mark_min_span_tree_root( candidate_edge_heap ) {
    this.span_parent = this;
    _(this.neighbor_edges).each(function insert_edge( next_edge ) {
      candidate_edge_heap.push(next_edge);
    });
  };

  this.is_in_min_span_tree = function is_in_min_span_tree() {
    return this.span_parent != null;
  };

  this.get_id = function get_id() {
    return this.id;
  };

  this.get_x = function get_x() {
    return this.x;
  };

  this.get_y = function get_y() {
    return this.y;
  };

  this.add_neighbor_edge = function add_neighbor_edge(p2, dist) {
    this.neighbor_edges.push(new EdgeContext(this, p2, dist));
    p2.neighbor_edges.push(new EdgeContext(p2, this, dist));
  }

  this.sort_neighbor_edges = function sort_neighbor_edges() {
    this.neighbor_edges = _(this.neighbor_edges).sortBy('dist');
  };

  this.each_neighbor_until = function each_neighbor_until(lambda) {
    _(this.neighbor_edges).any(lambda);
  }

  return this;
}

function EdgeContext( p1, p2, dist ) {
  this.from = p1;
  this.to = p2;
  this.dist = dist;

  this.get_from = function get_from() {
    return this.from;
  };

  this.get_to = function get_to() {
    return this.to;
  };

  this.get_from_id = function get_from_id() {
    return this.from.id;
  };

  this.get_to_id = function get_to_id() {
    return this.to.id;
  };

  this.get_distance = function get_distance() {
    return this.dist;
  };

  this.add_to_min_span_tree = function add_to_min_span_tree(candidate_edge_heap) {
    this.from.span_children.push(this);
    this.to.span_parent = this.from;

    this.to.each_neighbor_until(function insert_edge_if_vertex_not_linked(next_edge) {
      if( next_edge.to.is_in_min_span_tree() == false ) {
        candidate_edge_heap.push(next_edge);
      }

      // All neighbor edges should be visited, so unconditionally return false.
      return false;
    });
  }

  return this;
}
