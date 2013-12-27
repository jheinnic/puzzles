/** 
* The 'sequential salesman' traverses all the points in the order they are given
* in the graph. Not efficient, but easy to implement. 
*/
function JCHSalesman( ) {
  this.graph = {};
  this.vertex_state_by_id = {};

  this.get_point_by_id = function get_point_by_id( point_id ) {
    return this.vertex_state_by_id[point_id];
  };

  // For the sake of comparing distances, we can omit the square root because for any pair of distance
  // metrics, m and n, dist-of-m < dist-of-n, implies that dist-of-m^2 < dist-of-n^2.
  this.get_dist_squared = function get_dist_squared(point1, point2) {
    return Math.pow(point2.x - point1.x, 2) + Math.pow(point2.y - point1.y, 2);
  };

  this.has_edge_between = function has_edge_between(p1, p2) {
    return _(p1.adjacent_weights).any(function(p1Adj) {
    });
  });
  };

  this.init_graph = function init_graph( graph ) {
    this.graph = graph;
    var self = this;
    _(graph.points).each(function(p) {
      self.vertex_state_by_id[p.id] = {
        point: p,
        in_span_tree: 0,
        adjacent_weights: [],
        span_children: []
      };
    });
    
    _(graph.arcs).each(function( a ) {
      var p1 = self.get_point_by_id(a[0]);
      var p2 = self.get_point_by_id(a[1]);
      var dist_squared = self.get_dist_squared( p1.point, p2.point );

      // NOTE: An indexed representation, either as an object, with "to" vertex IDs as keys, or as a sparse array,
      //       with each vertex assigned a unique index, were considered, but there seemed to be very little use for
      //       indexed access of the metadata for a specific coordinate pair given both coordinates, only for complete
      //       rows or columns of metadata, given a single coordinate.  AS such, a non-sparse array of unordered records
      //       is used now instead.  There is one case near the end where indexed access would be useful.  Perhaps this
      //       would be a fine reason to keep the edge lists in sorted order, enabling lookup by binary search--a
      //       reasonable compromise between the relative importance and demands on space and time here.
      p1.adjacent_weights.push({ from: p1, to: p2, dist_squared: dist_squared });
      p2.adjacent_weights.push({ from: p2, to: p1, dist_squared: dist_squared });
    });
  };
  
  this.compute_plan = function compute_plan( graph, start_point_id ) {
    // Init
    this.init_graph(graph);
    var start_point = this.get_point_by_id(start_point_id);

    // Compute a minimal span tree
    this.compute_minimal_span_tree(start_point);

    // Perform a DFS of the span tree to derive a cycle, and as a heuristic, attempt to replace all paths consisting
    // of back edges with alternate routes that connect the same end points, but do so at reduced cost, perhaps even
    // by a direct edge.
    var retVal = this.compute_derived_cycle(start_point);

    // console.debug('Computation result: ');
    // console.debug(retVal);

    return retVal;
  };

  this.compute_minimal_span_tree = function compute_minimal_span_tree( start_point ) {
    var candidate_edge_heap = new Heap(function(a, b) {
      return a.dist_squared - b.dist_squared;
    });

    // Prepare for Prim's minimum spanning tree algorithm.  Populate a binary heap with
    // adjacency information from the given root of the desired tree, start_point.
    start_point.in_span_tree = 1;
    _(start_point.adjacent_weights).each(function(adjacency) {
      candidate_edge_heap.push(adjacency);
    });

    // Iterate once per vertex that remains in the graph.  Each iteration will select the
    // least costly edge from the binary heap that connects an unconnected vertex to the spanning tree.
    _(this.graph.points.length - 1).times( function() {
      var best_new_edge = candidate_edge_heap.pop();
      while( best_new_edge.to.in_span_tree == 1 ) {
        best_new_edge = candidate_edge_heap.pop();
      }

      // Mark the chosen vertex as now attached to the minimum spanning tree and track the edge that connected
      // it as part of the spanning tree under construction as well.
      var next_vertex = best_new_edge.to;
      best_new_edge.from.span_children.push(next_vertex);
      next_vertex.in_span_tree = 1;

        // Load the binary heap with information about edges leading from the newly added vertex, candidate
        // edges that are now reachable for inclusion through it.
      _(next_vertex.adjacent_weights).each(function(adjacency) {
        if( adjacency.to.in_span_tree == 0 ) {
          candidate_edge_heap.push(adjacency);
        }
      });
    })
  };

  // A depth first traversal of a minimum spanning tree produces a tour.  It will not be optimal due to the
  // back edge traversal involved, but heuristics can be applied to negate much of this overhead.  This algorithm
  // may not provide a perfectly optimal result, but it should produce a good approximation in most cases.
  this.compute_derived_cycle = function compute_derived_cycle( start_point ) {
    var return_cycle = [];

    this.derived_cycle_recursion(return_cycle, [], start_point);
    return_cycle.push( start_point.point.id );

    return return_cycle;
  };

  this.derived_cycle_recursion = function derived_cycle_recursion( cycle_path, back_step_path, from_vertex ) {
    back_step_path.push(from_vertex);
    cycle_path.push(from_vertex.point.id);

    var self = this;
    var children = from_vertex.span_children;
    // Do not step back to the from_vertex as recursion unwinds.  Instead, rely on logic that precedes each
    // subsequent forward step and applies a heuristic to optimize unnecessary back-steps into shorter paths.
    // The best optimization is a direct adjacency from the first vertex the tree traversal back-steps from that
    // lands where the next forward edge traversal will be heading.  The next best optimization is a shortest
    // path through other nodes that still has an overall cost less than the original back-stepping path.  If
    // neither exists, we have to use the back-stepping path from the minimum spanning tree traversal as-is.
    if( children.length >= 1 ) {
      self.derived_cycle_recursion(cycle_path, back_step_path, _(children).first());
    }
    _.chain(children).rest().each(function(to_vertex) {
      // Before advancing a forward edge, check whether we need to account for back_steps from the spanning
      // tree's depth first traversal.  If we have had to step back, let the path from the deepest ancestor
      // to this call stack frame's from_vertex, to this call stack frame's for loop's upcoming to_vertex
      // represent a worst-case boundary and search for a
      var origin = back_step_path.pop();
      if( origin != from_vertex ) {
        var current = origin;
        // var worst_case_path = [];
        var worst_case_cost = 0;

        while( current != from_vertex ) {
          console.debug( "CurrentVertex, " + current.point.id + ", is not FromVertex, " + from_vertex.point.id );

          var next = back_step_path.pop();

          // Leverage Euclidean and undirected symmetries.  Weight(current->next) == Weight(next->current)
          // TODO: Because the adjacency lists are not indexed, presume that computing the squared distance is
          //       cheaper than searching for the given adjacency.
          // TODO: Later, refactor so that each node describes its spanning tree neighbors by listing the edges
          //       to those neighbors, not just the neighbor vertices, because that way we can just re-use the
          //       edge-cached copy of dist_squared.
          worst_case_cost += self.get_dist_squared(current.point, next.point);

          // NOTE: Only needed for debug messaging, but potentially worth knowing how to construct this
          //       down the road, so leave it present by commented out.
          // Track the path back as we measure it so we know what it is if we find no shorter path from
          // the ancestor from which we made the first unaccounted back_step to the upcoming forward to_vertex
          /*
           * worst_case_path.push(next);
           */

          // Advance the iteration, working back towards from_vertex.  The back_step path is populated by
          // appending to the right, so the partial reverse path is inferred by popping elements off the
          // right hand array end.
          current = next;
        }

        // Add the cost to make the last step connecting from_vertex, the last vertex we've back-stepped into,
        // with to_vertex, the un-visited one we wish to reach next, establishing the total cost plus overhead for
        // taking the back-stepping route as-is.
        worst_case_cost += self.get_dist_squared(current.point, to_vertex.point);

        // console.debug(
        //   "Optimizing a backward traversal path from " + origin.point.id +
        //   " to " + to_vertex.point.id + " with maximum cost " + worst_case_cost +
        //   " for partial back edge path: ");
        // console.debug(worst_case_path)

        // The best case scenario would be a direct edge from origin to to_vertex.  The shortest distance
        // between any two points in a Euclidean plane is a straight line.  There may not be a direct
        // adjacency, but even so there may be a shorter path from back_step origin to the next to_vertex
        // other than the worst-case-scenario of reversing the original path from from_vertex to back_step
        // origin.
        if(self.has_edge_between(origin, to_vertex) == false) {
          _(self.get_path_between(origin, to_vertex, worst_case_cost)).each(function(back_vertex) {
              cycle_path.push(back_vertex.point.id);
              // console.log( "During back_step handling, append BackVertex to cycle: " + back_vertex.point.id );
          })
        }
      }

      back_step_path.push(from_vertex);
      self.derived_cycle_recursion(cycle_path, back_step_path, to_vertex);
    });
  };

  this.get_path_between = function get_path_between( start_point, end_point, worst_case_cost ) {
    var self = this;

    // Breadth First Search. 
    // The 'visit_queue' consists of the current point, and a 'breadcrumb' path back to the start point.
    var visit_queue = [[start_point, [], 0]];
    var visited = {};
    var closest_path = null;
    var closest_dist = 10000000;
    
    // We're going to BFS for the end_point.  It's not guaranteed to be the shortest path.
    // Is there a better way that is computationally fast enough?
    while(visit_queue.length > 0) {
      var a = visit_queue.shift();
      var this_point = a[0];
      var this_path = a[1];
      var this_dist = a[2];
      visited[this_point.point.id] = true;
      
      if (this_point.point.id == end_point.point.id) {
        // We've arrived, return the breadcrumb path that took us here...
        if (this_dist < closest_dist) {
          closest_dist = this_dist;
          closest_path = this_path;
        }
      } else {
        // Otherwise, explore all the surrounding points...
        new_points = this_point.adjacent_weights;
        _(new_points).each(function(adj) {
          if (!visited[adj.to.point.id]) {
            dist_next = adj.dist_squared + this_dist;
            if( dist_next <= worst_case_cost ) {
              visit_queue.push([adj.to, this_path.concat(adj.to), dist_next]);
            }
          }
        }); 
      }  
    }
    
    // Otherwise, a path doesn't exist
    if (closest_path == null) {
     throw( "Could not compute path from *" + start_point.point.id + "* to *" + end_point.point.id + "*, but should have at least found original back-step path!" );
    }

    // Prune the last element from the list to make it easier to generalize the visitation of end_point between
    // cases with the help of either a local a social worker or as an educated homeowner and consumer.
    var retVal = _.initial(closest_path);
    // console.debug( "Shortest path from " + start_point.point.id + " to " + end_point.point.id + " is through: " );
    // console.debug( retVal );
    return retVal;
  };

  return this;
}
