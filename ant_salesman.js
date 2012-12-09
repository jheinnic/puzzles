/** 
* Basic idea (w/o pheromons):
* http://www.idsia.ch/~luca/acs-bio97.pdf
* http://joel.inpointform.net/software-development/traveling-salesman-ant-colony-optimization-javascript-solution/
*/

function AntSalesman() {
    this.num_ants = 20;
    this.bfs_depth = 4;

    this.distances = [];
    this.visited = [];

    this.get_dist = function(point1, point2) {
        return Math.sqrt(Math.pow(point2.x - point1.x, 2) + Math.pow(point2.y - point1.y, 2));
    };

    // point to index
    this.ptoi = function(point) {
        return parseInt(point.substr(3), 10);
    };

    // BFS from one point to another (force=true ignores the visited array and the bfs_depth)
    this.get_path = function(start, end, force) {
        // check if points are connected
        var direct_distance = this.distances[start][end];
        if (direct_distance !== Infinity) {
            return {distance: direct_distance, path: [end]};
        }

        var remaining_depth = this.bfs_depth;
        var visited = this.visited;
        // we must find the endpoint, no deepness limit, ignore visited
        if (force) {
            remaining_depth = 1000000;
            visited = [];
        }

        // queue element: [point_id, [path, to, point], distance]
        var queue = [[start, [], 0]];
        while (queue.length > 0 && remaining_depth > 0) {
            remaining_depth -= 1;
            var point = queue.shift();
            var pid = point[0];
            var path = point[1];
            var distance = point[2];

            // found?
            if (pid === end) {
                return {distance: distance, path: path};
            }

            // not found yet, go deeper
            for (var i=0; i < this.distances[pid].length; i++) {
                if (this.distances[pid][i] !== Infinity && !visited[i]) {
                    var new_path = path.concat();
                    new_path.push(i);
                    distance += this.distances[pid][i];
                    queue.push([i, new_path, distance]);
                }
            }
        }

        // no result
        return null;
    };

    this.compute_plan = function(graph, start_point_id) {
        var self = this;
        var num_points = graph.points.length;
        var start_point = this.ptoi(start_point_id);
        var best_path = [];
        var best_distance = Infinity;
        var i;

        // initialize distances array
        for (i=0; i < num_points; i++) {
            this.distances[i] = [];
            for (var j=0; j < num_points; j++) {
                this.distances[i][j] = Infinity;
            }
        }
        _(graph.arcs).each(function(a) {
            var i = self.ptoi(a[0]);
            var j = self.ptoi(a[1]);
            self.distances[i][j] = self.get_dist(graph.points[i], graph.points[j]);
            self.distances[j][i] = self.distances[i][j];
        });

        // send ants
        for (var ant=0; ant < this.num_ants; ant++) {
            var current = start_point;
            this.visited = new Array(num_points);
            this.visited[current] = true;
            var path = [current];
            var distance = 0;

            var path_by_point = {};
            for (var step=0; step < num_points; step++) {
                // calculate probabilities of next
                var probs = new Array(num_points);
                var sum_probs = 0;
                for (var point=0; point < num_points; point++) {
                    probs[point] = 0;
                    if (!this.visited[point] && current !== point) {
                        path_by_point[point] = this.get_path(current, point, false);
                        if (path_by_point[point] !== null) {
                            // probability is inverse proportinal to distance
                            probs[point] = 1.0 / path_by_point[point].distance;
                        }
                    }
                    sum_probs += probs[point];
                }

                // choose next
                var next = -1;
                var rand = Math.random() * sum_probs;
                for (i=0; i < num_points; i++) {
                    if (!this.visited[i]) {
                        rand -= probs[i];
                        if (rand <= 0) {
                            next = i;
                            break;
                        }
                    }
                }

                // cannot go forward? force choosing next
                if (sum_probs === 0) {
                    // choose start point by default
                    next = start_point;
                    // choose first unvisited
                    for (i=0; i < num_points; i++) {
                        if (!this.visited[i]) {
                            next = i;
                            break;
                        } 
                    }
                    path_by_point[next] = this.get_path(current, next, true);
                }

                // next chosen, add to path
                distance += path_by_point[next].distance;
                _(path_by_point[next].path).each(function(point) {
                    self.visited[point] = true;
                    path.push(point);
                });
                current = next;

                // are we back?
                if (next === start_point) {
                    break;
                }
            }

            // is it better than others?
            if (distance < best_distance) {
                best_distance = distance;
                best_path = path;
            }
        }

        // map point ids
        var result_path = _(best_path).map(function(p) {
            return "pt_"+ String(p);
        });
        return result_path;
    };
}