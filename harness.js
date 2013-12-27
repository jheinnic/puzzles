/**
* The harness is responsible for actually running algorithms and computing 
* the distance, etc. We also make sure the algorithms don't break any rules,
* like trying to traverse non-existant arcs. 
**/
function Harness() {
  
  this.get_dist = function(point1, point2) {
    return Math.sqrt(Math.pow(point2.x - point1.x, 2) + Math.pow(point2.y - point1.y, 2));
  }
  
  
  this.get_point = function(point_id, graph) {
    // This is inefficient. Is there a faster way? 
    return _(graph.points).detect(function(p) {
      return(p.id == point_id)
    })
  }
  
  
  this.arc_exists = function(point1, point2, graph) {
    // This is pretty inefficient too, given the calling context. Better way?
    return _(graph.arcs).detect(function(a) {
      return (a[0] == point1.id && a[1] == point2.id) || (a[1] == point1.id && a[0] == point2.id);
    })
  }
  
  
  this.compute_plan_cost = function(graph, plan) {
    
    // Init
    visited = {}
    running_length = 0
    start_time = new Date();
    last_point = null;
    
    // Visit each point sequentially, add up the total distance travelled by the salesman...
    for(var i=0; i<plan.length; i++) {
      
      point_id = plan[i];
      point = this.get_point(point_id, graph);
      if (point == null) throw "Unknown point!"
      if (i == plan.length-1 && point_id != plan[0]) throw "The salesman must return to the starting point!"
      
      if (last_point) {
        running_length += this.get_dist(last_point, point);
        if (!this.arc_exists(point, last_point, graph)) throw "Tried to traverse a non-existing arc! " + last_point.id + " -> " + point.id
      }
      
      last_point = point;
      visited[point_id] = true 
    }
    
    // Have we visited all points in the graph? 
    _(graph.points).each(function(p) {
      if (!visited[p.id]) throw "Not all points have been visited! " + p.id
    })
    
    return running_length;
  }
  
  
  this.run_algorithm = function(graph, start_point_id, algo) {
    
    // Sanity check..
    if (algo == null) throw "No algorithm given!"
    if (algo.compute_plan == null) throw "You must implement algo.compute_plan(...)!"
    
    
    // Run the algorithm...
    var start_time = new Date();
    var plan = algo.compute_plan(graph, start_point_id);
    var end_time = new Date();
    
    // Make sure it's reasonably fast, and then compute the total length
    var MAX_TIME = 10*1000;  // 10 seconds  (3 seconds is way too long, but some machines are slow.
                             // Bonus: blow us away with your solution and we'll get you a screaming
                             // fast machine. 
    var delta = end_time - start_time;
    if (delta > MAX_TIME) throw "Your algorithm took " + delta + "ms, too long to run!";

    console.log( "Algorithm took " + delta + "ms to run." );


    
    return plan
  }
  
  
  
}

