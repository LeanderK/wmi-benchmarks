import argparse
import os
import random

import networkx as nx
import pysmt.shortcuts as smt

from wmibench.io import Density

def unit_hypercube_bounds(variables):
    return {x : [0,1] for x in variables}
    


def make_distinct_bounds(variables):
    base_lower_bound = 0.13
    base_upper_bound = 0.89
    step = 0.01

    bounds = smt.TRUE()
    for xi in variables:
        bounds &= xi >= base_lower_bound + i * step  # - i * step
        bounds &= xi <= base_upper_bound - i * step  # + i * step

    return bounds


def xor(n):

    x = smt.Symbol('x', smt.REAL)
    xis = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]
    variables = [x] + xis
    
    terms = [x <= xi for xi in xis]
    xor = smt.FALSE()
    for term in terms:
        xor = (xor | term) & ~(xor & term)

    support = xor & make_distinct_bounds(variables)
    weight = smt.Real(1.0)

    return Density(support, weight, domain=unit_hypercube_bounds(variables))


def mutual_exclusive(n):
    
    x = smt.Symbol('x', smt.REAL)
    xis = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]
    variables = [x] + xis

    terms = [x <= xi for xi in xis]
    disjunction = smt.TRUE()
    for i in range(n):
        for j in range(i + 1, n):
            disjunction &= ~terms[i] | ~terms[j]

    disjunction = smt.simplify(disjunction) & smt.Or(*terms)

    support = disjunction & make_distinct_bounds(variables)
    weight = smt.Real(1.0)
    return Density(support, weight, domain=unit_hypercube_bounds(variables))


def dual_paths(n):

    variables = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]
    
    terms = []
    for i in range(n):
        v1, v2 = random.sample(variables, 2)
        terms.append(v1 * random.random() <= v2 * random.random())

    paths = []
    for i in range(n):
        paths.append(smt.And(*random.sample(terms, n)))

    support = smt.Or(*paths) & smt.And(*[(x >= 0.0) & (x <= 1.0) for x in variables])    
    weight = smt.Real(1.0)
    return Density(support, weight, domain=unit_hypercube_bounds(variables))


def dual_paths_distinct(n):

    variables = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]

    terms = []
    for i in range(n):
        v1, v2 = random.sample(variables, 2)
        terms.append(v1 * random.random() <= v2 * random.random())

    paths = []
    for i in range(n):
        paths.append(smt.Ite(smt.And(*random.sample(terms, n)), smt.Real(i), smt.Real(0)))

    support = smt.And(*[(x >= 0.0) & (x <= 1.0) for x in variables])
    weight = smt.Plus(*paths)
    return Density(support, weight, domain=unit_hypercube_bounds(variables))


def click_graph(n):

    def ind(c):
        return smt.Ite(c, smt.Real(1), smt.Real(0))

    sim = [smt.Symbol(f'sim_{i}', smt.BOOL) for i in range(n)]
    cl = [[smt.Symbol(f'cl_{i}_{j}', smt.BOOL) for j in (0, 1)] for i in range(n)]
    b = [[smt.Symbol(f'b_{i}_{j}', smt.BOOL) for j in (0, 1)] for i in range(n)]
    sim_x = smt.Symbol('sim_x', smt.REAL)
    b_x = [[smt.Symbol(f'b_x_{i}_{j}', smt.REAL) for j in (0, 1)] for i in range(n)]

    support = smt.And([
        smt.Iff(cl[i][0], b[i][0])
        & smt.Iff(cl[i][1], (sim[i] & b[i][0]) | (~sim[i] & b[i][1]))
        for i in range(n)
    ])

    w_sim_x = ind(sim_x >= 0) * ind(sim_x <= 1)
    w_sim = [smt.Ite(s_i, sim_x, 1 - sim_x) for s_i in sim]
    w_b_x = [ind(b_x[i][j] >= 0) * ind(b_x[i][j] <= 1)
             for i in range(n) for j in (0, 1)]
    w_b = [smt.Ite(b[i][j], b_x[i][j], 1 - b_x[i][j])
           for i in range(n) for j in (0, 1)]

    weight = smt.Times(*([w_sim_x] + w_sim + w_b_x + w_b))
    return Density(support, weight, domain=unit_hypercube_bounds(variables))


def univariate(n):

    variables = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]

    domain = {x : [-2, 2] for x in variables}
    support = smt.And(*[x > 0.5 for x in variables])
    weight = smt.Times(*[smt.Ite((x > -1) & (x < 1), smt.Ite(x < 0, x + smt.Real(1), -x + smt.Real(1)), smt.Real(0))
                         for x in variables])

    return Density(support, weight, domain=domain)


def dual(n):
    n = 2 * n
    variables = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]

    terms = [variables[2 * i] <= variables[2 * i + 1]
             for i in range(int(n / 2))]

    disjunction = smt.Or(*terms)

    for i in range(len(terms)):
        for j in range(i + 1, len(terms)):
            disjunction &= ~terms[i] | ~terms[j]

    support = disjunction & smt.And(*[(x >= 0.0) & (x <= 1.0) for x in variables])
    weight = smt.Real(1)
    return Density(support, weight, domain=unit_hypercube_bounds(variables))


def and_overlap(n):

    variables = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]
    terms = [variables[i] <= variables[i + 1] for i in range(n - 1)]
    support = smt.And(*terms) & smt.And(*[(x >= 0.0) & (x <= 1.0) for x in variables])
    weight = smt.Real(1)
    return Density(support, weight, domain=unit_hypercube_bounds(variables))


def make_from_graph(graph):
    n = len(graph.nodes)
    variables = [smt.Symbol(f'x{i}', smt.REAL) for i in range(n)]
    
    support = smt.And(*((variables[i] + 1 <= variables[j]) |
                        (variables[j] <= variables[i] - 1)
                        for i, j in graph.edges))
    support = support & smt.And(*[(x >= -1.0) & (x <= 1.0) for x in variables])
    weight = smt.Real(1)
    domain = {x : [-1, 1] for x in variables}
    return Density(support, weight, domain=domain)


def tpg_star(n):
    g = nx.Graph()
    for i in range(1, n):
        g.add_edge(0, i)
    return g


def tpg_3ary_tree(n, arity=3):
    g = nx.Graph()
    e = 1
    depth = 1
    while e < n:
        to_add = min(arity ** depth, n - e)
        for i in range(to_add):
            source = i // arity + e - arity ** (depth - 1)
            target = e + i
            g.add_edge(source, target)
        e += to_add
        depth += 1

    return g


def tpg_path(n):
    g = nx.Graph()
    for i in range(n - 1):
        g.add_edge(i, i + 1)
    return g


problem_generators = {
    'xor': xor,
    'mutex': mutual_exclusive,
    'click': click_graph,
    'uni': univariate,
    'dual': dual,
    'dual_paths': dual_paths,
    'dual_paths_distinct': dual_paths_distinct,

    'and_overlap': and_overlap,

    'tpg_star': lambda n: make_from_graph(tpg_star(n)),
    'tpg_3ary_tree': lambda n: make_from_graph(tpg_3ary_tree(n)),
    'tpg_path': lambda n: make_from_graph(tpg_path(n)),
}


def get_problem(problem_name):
    if problem_name in problem_generators:
        return problem_generators[problem_name]
    else:
        raise ValueError("No problem with name {}".format(problem_name))


def generate_benchmark(sizes, seeds, output_folder):

    for seed in seeds:
        for size in sizes:
            generator = get_problem(problem_name)
            random.seed(seed)
            density = generator(size)
            filename = os.path.join(output_folder, "{}_{}".format(problem_name, size))
            if seed is not None:
                filename += "_{}".format(seed)

            density.to_file(f'{filename}.json')


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("problem_name", type=str, choices=problem_generators.keys())
    parser.add_argument("size", type=str)
    parser.add_argument("-s", "--seed", default=None)
    parser.add_argument("--output_folder", default=None)

    args = parser.parse_args()

    if args.output_folder is None:
        args.output_folder = os.path.join(os.getcwd(), 'structured')

    if ":" in args.size:
        first, last = args.size.split(":", 1)
        sizes = range(int(first), int(last) + 1)
    else:
        sizes = [int(args.size)]

    problem_name = args.problem_name

    if args.seed is not None and ":" in args.seed:
        first, last = args.seed.split(":", 1)
        seeds = range(int(first), int(last) + 1)
    else:
        seeds = [int(args.seed) if args.seed is not None else None]

    if not os.path.isdir(args.output_folder):
        os.mkdir(args.output_folder)

    generate_benchmark(sizes, seeds, args.output_folder)
