from collections import deque
from collections import defaultdict
from itertools import combinations
import logging
import argparse


# A class to represent a graph. A graph
# is the adjacency list implemented
# as a dictionary.
class Graph:
    def __init__(self, vertices1, vertices2, graph_structure=None):
        """
        initialization of class Graph
        :param vertices1: first set (U) of vertices
        :param vertices2: second set (V) of vertices
        :param graph_structure: (optional) dictionary of values {u:[[v_1, cost1], [v_2, cost2], ... ], ...}
        """
        self.U = vertices1
        self.V = vertices2
        self.nodes = set(self.U + self.V)
        # assert len(self.V) == len(self.U), "vertex sets unequal!"
        self.graph = defaultdict(list)
        self.edges = set()
        self.costs = defaultdict(int)
        self.matching_list = []
        self.matching_best = None

        if graph_structure:
            for item in graph_structure.items():
                node1, neighbours = item
                for neighbour in neighbours:
                    node2, cost = neighbour
                    self.add_edge(node1, node2, cost)

    def __eq__(self, other):
        return set(self.graph) == set(other.graph)

    def __iadd__(self, other):
        if isinstance(other, tuple):
            u, v, cost = other
            if (u, v) not in self.edges and v in self.V and u in self.U:
                self.add_edge(u, v, cost)
        elif isinstance(other, list):
            for element in other:
                self.__iadd__(element)
        return self

    def add_edge(self, u, v, cost=0):
        """
        Adds an undirected edge from u to v with weight cost
        :param u: node1
        :param v: node2
        :param cost: (optional) set to 0 if not given
        :return: None
        """
        if u not in self.U + self.V:
            raise ValueError("node %s not in vertex set" % u)
        if v not in self.U + self.V:
            raise ValueError("node %s not in vertex set" % v)
        self.graph[u].append((v, cost))  # (a,b) <--> (b,a) since its a digraph
        self.graph[v].append((u, cost))
        self.edges.add((u, v))
        self.edges.add((v, u))
        self.costs[(u, v)] = cost
        self.costs[(v, u)] = cost

    def adj_list(self):
        return self.graph

    def get_edges(self):
        return self.edges

    def get_costs(self):
        return self.costs

    def get_cost(self, cost_obj=None):
        cost = 0
        if self.matching_best:
            best = self.matching_list[self.matching_best]
            if cost_obj:
                if isinstance(cost_obj, dict):
                    cost = sum(cost_obj[(key, val)] for key, val in best.items())
                elif isinstance(cost_obj, list):
                    cost = sum(cost_obj[val - len(cost_obj)][key] for key, val in best.items())
                else:
                    raise TypeError("Illegal data type %s" % str(type(cost_obj)))
                return cost
            cost = sum(self.costs[(key, val)] for key, val in best.items())
        return cost

    def is_matching(self, given_matching):
        """
        Validates if a given matching is proper
        :param given_matching: dictionary in the form {u: v, ...}
        :return: Boolean
        """
        invMatching = {}
        for item in given_matching.items():
            u, v = item
            if (u, v) not in self.edges or u not in self.U or v not in self.V:
                return False
            invMatching[v] = u
        if len(invMatching) == len(given_matching):
            if given_matching not in self.matching_list:
                self.matching_list.append(given_matching)
            return True
        return False

    def is_perfect_matching(self, given_matching):
        """
        Validates if a given matching is perfect
        :param given_matching: dictionary in the form {u: v, ...}
        :return: Boolean
        """
        if self.is_matching(given_matching) and len(given_matching) == min(len(self.U), len(self.V)):
            self.matching_best = self.matching_list.index(given_matching)
            return True
        return False

    def find_first_unmatched(self, given_matching=None):
        """
        Finds the first node from set U that is free
        :param given_matching: (optional) dictionary in the form {u: v, ...}
               if no matching is given, selects the largest available imperfect matching
        :return: node or None if no node is found
        """
        if not given_matching:
            # if no matching is given, select the largest imperfect from the list
            try:
                given_matching = max([imperfect for imperfect in self.matching_list
                                      if self.matching_list and not self.is_perfect_matching(imperfect)],
                                     key=lambda item: len(item))
            except ValueError:
                return min(self.U)
        elif not self.is_matching(given_matching) or self.is_perfect_matching(given_matching):
            return None

        return min([u for u in self.U if u not in given_matching.keys()])


def get_path(pred, v):
    path = [v]
    while pred[v] != -1:
        path.append(pred[v])
        v = pred[v]
    path.reverse()
    return path


def augmenting_path_bfs(graph, node, current_matching, prices, lvl=logging.ERROR):
    # logger conf
    logger = logging.getLogger("aug_path_bfs")
    logger.setLevel(lvl)

    # G = [ [U,V], [(edge,cost)...] ]
    q = deque()

    # using dict as array
    visited = {}  # dict.fromkeys(graph.nodes, False)
    pred = {}

    # sets
    odd_nodes = set()
    even_nodes = set()

    for u in graph.nodes:
        visited[u] = False
        pred[u] = -1

    q.append(node)
    q.append(-1)

    level = 0
    while len(q) > 1:
        logger.info("Queue " + str(q))
        c = q.popleft()

        if c == -1:
            level = level + 1
            c = q.popleft()
            logger.info("Popped element " + str(c) + " after -1")
            q.append(-1)
        visited[c] = True
        if level % 2 == 0:  # we must start from even_node
            logger.info("even level " + str(level))
            next_level_odd = True
            even_nodes.add(c)
        else:
            logger.info("odd level " + str(level))
            next_level_odd = False
            odd_nodes.add(c)

        u = c
        for v in graph.adj_list()[c]:
            if not visited[v[0]] and graph.costs[(u, v[0])] \
                    == (prices.get(u, 0) + prices.get(v[0], 0)):
                logger.info("Matching " + str(current_matching) + " v[0]= " + str(v[0]))
                if next_level_odd and (v[0] not in current_matching.values() and v[0] not in current_matching.keys()):
                    pred[v[0]] = c
                    logger.info("Next level odd and %s not in matching" % str(v[0]))
                    augmenting_path = get_path(pred, v[0])
                    logger.info("Returning path: %s, odd: %s, even: %s" % (augmenting_path, odd_nodes, even_nodes))
                    return augmenting_path, odd_nodes, even_nodes
                if ((next_level_odd and current_matching.get(c) != v[0]) or
                    (not next_level_odd and (current_matching.get(c) == v[0] or current_matching.get(v[0]) == c))) \
                        and not v[0] in q:
                    q.append(v[0])
                    pred[v[0]] = c
    logger.info("Exiting.. odd: %s, even: %s" % (odd_nodes, even_nodes))
    return None, odd_nodes, even_nodes


def compute_delta(graph, odd_nodes, even_nodes, prices, lvl=logging.ERROR):
    # logger conf
    logger = logging.getLogger("computeDelta")
    logger.setLevel(lvl)
    try:
        d = min([graph.costs[(u, v)] - prices[u] - prices[v]
                 for u in even_nodes for v in graph.nodes.difference(odd_nodes)
                 if (u, v) in graph.edges])
    except ValueError:
        return 0
    return d


def hungarian_algorithm(graph, has_cost_array=False, lvl=logging.ERROR):
    # logger conf
    logger = logging.getLogger("hungarian_algorithm")
    logger.setLevel(lvl)

    current_matching = defaultdict(list)
    prices = dict.fromkeys(graph.nodes, 0)

    while not graph.is_perfect_matching(current_matching):
        node = graph.find_first_unmatched(current_matching)
        augmenting_path, odd_nodes, even_nodes = \
            augmenting_path_bfs(graph, node, current_matching, prices, lvl)
        if augmenting_path is not None:
            logger.info("augmenting path " + str(augmenting_path))
            new_matching = current_matching.copy()
            for i in range(0, len(augmenting_path) - 1, 2):  # augmenting path is a list
                new_matching[augmenting_path[i]] = augmenting_path[i + 1]
            current_matching = new_matching
            logger.info("matching " + str(current_matching))
            logger.info("Progress: %.2f%% (Matching %d / %d)"
                        % (len(current_matching) * 100 / len(graph.U), len(current_matching), len(graph.U)))
        else:
            d = compute_delta(graph, odd_nodes, even_nodes, prices, lvl)
            for u in even_nodes:
                prices[u] = prices[u] + d
            for u in odd_nodes:
                prices[u] = prices[u] - d
    if has_cost_array:
        inv_matching = {value: key for key, value in current_matching.items()}
        print(' '.join([str(inv_matching[item]) for item in range(len(current_matching), len(graph.nodes))]))
    return current_matching


def maximization(cost_array):
    if isinstance(cost_array, list):
        max_cost = max(max(cost_array, key=lambda cost_val: max(cost_val)))
        new_costs = []
        for item in cost_array:
            new_costs.append([(-1 * i) + max_cost for i in item])
    elif isinstance(cost_array, dict):
        max_cost = -100000
        for value in cost_array.values():
            for array in value:
                max_cost = array[1] if max_cost < array[1] else max_cost
        new_costs = defaultdict(list)
        for key, val in cost_array.items():
            new_costs[key] = []
            for arr in val:
                new_costs[key].append([arr[0], (-1 * arr[1]) + max_cost])
    else:
        raise TypeError("Illegal data type " + str(type(cost_array)))
    return new_costs


def decide_neighbors(node, size):
    """
    Decides neighboring tiles
    :param node: (i, j) for pixel coordinates
    :param size: (height, width)
    :return: list of neighboring tiles
    """
    x, y = node
    height, width = size
    height -= 1
    width -= 1
    neighbors = {(0, 0): [(0, 1), (1, 0)],
                 (0, width): [(0, width - 1), (1, width)],
                 (height, 0): [(height - 1, 0), (height, 1)],
                 (height, width): [(height - 1, width), (height, width - 1)]}

    for i in range(1, width):
        neighbors[(0, i)] = [(0, i + 1), (0, i - 1), (1, i)]
        neighbors[(height, i)] = [(height, i + 1), (height, i - 1), (height - 1, i)]

    for i in range(1, height):
        neighbors[(i, 0)] = [(i + 1, 0), (i - 1, 0), (i, 1)]
        neighbors[(i, width)] = [(i + 1, width), (i - 1, width), (i, width - 1)]

    if node in neighbors.keys():
        return neighbors[node]
    return [(x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1)]


def create_tiles(size):
    number_of_sets = size[0] * size[1] // 110
    first_set = list(combinations([i for i in range(10)], 2)) + [(i, i) for i in range(10)]
    all_sets = first_set.copy()
    all_sets += [(element[0] + 10 * num, element[1] + 10 * num)
                 for element in first_set for num in range(1, number_of_sets)]
    assert len(all_sets) // len(first_set) == number_of_sets
    return all_sets


def create_domino_portrait(lvl=logging.ERROR):

    # square_distance = lambda b1, d1: (b1 - d1) ** 2
    def square_distance(b1, d1):
        return (b1 - d1) ** 2

    # sum_square_distance = lambda p1, d1, p2, d2: \
    #     square_distance(grey_shade(p1), d1) + square_distance(grey_shade(p2), d2)
    def sum_square_distance(p1, d1, p2, d2):
        return square_distance(grey_shade(p1), d1) + square_distance(grey_shade(p2), d2)

    # domino_distance = lambda p1, d1, p2, d2: min(sum_square_distance(p1, d1, p2, d2),
    #                                              sum_square_distance(p1, d2, p2, d1))
    def domino_distance(p1, d1, p2, d2):
        return min(sum_square_distance(p1, d1, p2, d2), sum_square_distance(p1, d2, p2, d1))

    # weight = lambda u, v: square_distance(grey_shade(u), grey_shade(v))

    def weight(u, v):
        return square_distance(grey_shade(u), grey_shade(v))

    old_weights = {(i, j): [[n, weight((i, j), n)] for n in decide_neighbors((i, j), input_size)]
                   for i in range(input_size[0]) for j in range(input_size[1]) if not (i + j) % 2}
    new_weights = maximization(old_weights)
    graph_max = Graph([(i, j) for i in range(input_size[0]) for j in range(input_size[1]) if not (i + j) % 2],
                      [(i, j) for i in range(input_size[0]) for j in range(input_size[1]) if (i + j) % 2],
                      new_weights)
    max_matching = hungarian_algorithm(graph_max, lvl=lvl)
    max_cost = sum([weight(key, val) for key, val in max_matching.items()])

    # minimization problem inits
    domino_tiles = create_tiles(input_size)
    domino_pos = list(max_matching.items())
    graph_min = Graph(domino_tiles, domino_pos,
                      {tile: [[pos, domino_distance(pos[0], tile[0] % 10, pos[1], tile[1] % 10)]
                              for pos in domino_pos] for tile in domino_tiles})
    temp_matching = hungarian_algorithm(graph_min, lvl=lvl)
    min_cost = sum([domino_distance(pos[0], tile[0] % 10, pos[1], tile[1] % 10)
                    for tile, pos in temp_matching.items()])
    min_matching = defaultdict(tuple)
    for key, val in temp_matching.items():
        # editing domino tile orientation based on c metric
        if sum_square_distance(val[0], key[0], val[1], key[1]) > \
                sum_square_distance(val[0], key[1], val[1], key[0]):
            new_key = (key[1] % 10, key[0] % 10)
        else:
            new_key = (key[0] % 10, key[1] % 10)
        min_matching[val] = new_key

    temp_matching.clear()
    return max_matching, max_cost, min_matching, min_cost


def create_output(max_matching, min_matching, tiling_file=None, dominoes_file=None):
    tiling = args.input_file + "_tiles.txt" if not tiling_file else tiling_file
    with open(tiling, 'w') as fp:
        for key, val in max_matching.items():
            fp.write(str(key) + " " + str(val) + "\n")

    dominoes = args.input_file + "_dominoes.txt" if not dominoes_file else dominoes_file
    with open(dominoes, 'w') as fp:
        for key, val in min_matching.items():
            fp.write(str(key) + " : " + str(val) + "\n")


if __name__ == "__main__":
    # logger conf
    logging.basicConfig(level=logging.ERROR)
    root_logger = logging.getLogger(__name__)

    # arguments conf
    parser = argparse.ArgumentParser(description="creates domino portraits of greyscale images")
    parser.add_argument("input_file", help="cost array or shades of grey", type=str)
    parser.add_argument("-m", "--maximize", help="maximize cost of matching", action="store_true")
    parser.add_argument("-a", "--assignment", help="file of cost array", action="store_true")
    parser.add_argument("tiling_file", nargs="?", default=None, type=str,
                        help="destination file for domino portrait")
    parser.add_argument("dominoes_file", nargs="?", default=None, type=str,
                        help="destination file for domino pieces' positions")

    args = parser.parse_args()
    infile = args.input_file

    input_array = []
    with open(infile) as input_p:
        for line in input_p:
            input_array.append(list(map(int, line.rstrip().split(" "))))

    input_size = (len(input_array), len(input_array)) if len(input_array) == len(input_array[0]) \
        else (len(input_array), len(input_array[0]))
    logging.debug("size = " + str(input_size))

    if args.assignment:
        final_cost_array = maximization(input_array) if args.maximize else input_array
        input_graph = Graph([i for i in range(input_size[0])],
                            [i for i in range(input_size[0], 2 * input_size[0])],
                            {i: [[j, final_cost_array[j - input_size[0]][i]]
                                 for j in range(input_size[0], 2 * input_size[0])]
                             for i in range(input_size[0])})
        matching = hungarian_algorithm(input_graph, args.assignment)
        print(input_graph.get_cost(input_array))
    else:
        def grey_shade(p1):
            return input_array[p1[0]][p1[1]]
        matching, tile_cost, matching2, domino_cost = create_domino_portrait()
        print(tile_cost)
        print(domino_cost)
        create_output(matching, matching2, args.tiling_file, args.dominoes_file)
