/**
* Builds a random graph, which is a bit tricky. We can create random points, no problemo,
* but making sure every point is transitively connected to every other point presents 
* some challenges. 
* In this implementation, we make sure every disjoint component is connected to every
* other component. Is there a better, more elegant, more aesthetic way to do this? 
**/
function RandomGraphBuilder() {
  
  NUM_POINTS = 75;
  NUM_ARCS = NUM_POINTS * 3;
  MAX_X = 100;
  MAX_Y = 100;
  
  this.get_point = function(point_id) {
    return _(this.graph.points).detect(function(p) {
      return(p.id == point_id)
    })
  }
  
  
  this.build_graph = function() {
    
    // Init 
    this.graph = {
      'points': [],
      'arcs': []
    }
    
    // First pass, just build some random points and random arcs...
    this.build_random_components();
    
    // Last pass, make sure everything is strongly connected
    this.connect_components();
    
    // Fin
    return this.graph;
  }
  
  
  
  this.build_random_components = function() {
    
    // Make some random points... 
    for(i=0; i<NUM_POINTS;i++) {
      this.graph.points.push({
        "id": "pt_" + String(i),
        "x": Math.random() * MAX_X,
        "y": Math.random() * MAX_Y
      })
    }
    
    // Now, let's make some random arcs...
    used_arcs = {}
    for(i=0;i<NUM_ARCS;i++) {
      
      pt1 = "pt_" + Math.floor(Math.random() * NUM_POINTS);
      pt2 = "pt_" + Math.floor(Math.random() * NUM_POINTS);
      
      // Don't have a self-looping arc...
      if (pt1 == pt2) { i--; continue; }
      
      // Have we already seen an arc like this? 
      arc_id_forward = pt1 + "_" + pt2
      if (used_arcs[arc_id_forward]) { i--; continue; }
  
      // What about the other way around? 
      arc_id_backward = pt2 + "_" + pt1
      if (used_arcs[arc_id_backward]) { i--; continue; }
      
      // All checks pass, let's go ahead and add this arc
      this.graph.arcs.push([pt1, pt2])
      used_arcs[arc_id_forward] = true
    }
  }
  
  
  this.connect_components = function() {
    
    var self = this;
    
    // Helper fn to just get the surounding points 
    var get_surrounding_points = function(point) {
      var a = _(self.graph.arcs).map(function(a) {
        if (a[0] == point.id) return a[1];
        if (a[1] == point.id) return a[0];
        return null;
      })
      return _.compact(a).map(function(pid) {
        return self.get_point(pid);
      });
    }
    
    // Traverses the graaph from a given point and marks each point it touches in the 'visited' hash
    var recurse_touch = function(point, visited) {

      // 'Touch' this point
      visited[point.id] = true
      
      _(get_surrounding_points(point)).each(function(p) {
        if (!visited[p.id]) {
          // We haven't visited this point. Let's 'touch' it.. (and recurse)
          recurse_touch(p, visited);
        } else {
          // Else, we have already visited this point, so do nothing
        }
      });
    }
    
    // Takes the diff between the graph.points and visited points to see which points we haven't visited 
    var get_first_unvisited_point = function(visited) {
      
      for(i=0;i<self.graph.points.length;i++) {
        point = self.graph.points[i];
        if (visited[point.id] == null) {
          // This point isn't in 'visited', so we haven't touched it...
          return point;
        }
      }
      
      // Else, we've touched everything... 
      return null
    }
    
    // We're going to loop until every component in the graph is connected... 
    while(true) {
      
      // Traverse the graph and build the 'visited' hash
      first_point = this.graph.points[0];
      visited = {}
      recurse_touch(first_point, visited);
      
      // Now, let's find a point we haven't touched yet (if any..)
      untouched_point = get_first_unvisited_point(visited);
      
      if (untouched_point) {
        
        // We have an untouched point... so let's go ahead and create an arc between this and a touched point.
        // Note: this has the unruly side-effect that all the components will be connected by the single 'first_point'.  Not ideal, but screw it.
        this.graph.arcs.push([first_point.id, untouched_point.id])
        
        // Now we have an arc between the 'visited' component and at least one other disjoint component.  We'll need to run 
        // through the cycle again (aka the while loop) until we've visited every point in the graph. 
        
      } else {
        // Otherwise, we've touched every point. We're done! 
        return;
      }
    }
  
  }
  
}
