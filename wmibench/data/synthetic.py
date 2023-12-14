import numpy as np
from pysmt.shortcuts import And, LE, Plus, Real, Times, is_sat

from scipy.linalg import solve as solve_linear_system


def generate_random_queries(domain, nqueries, qhardness, seed, support=None):
    """Generates 'nqueries' oblique queries by sampling an hyperplane
    intersecting with the axis-aligned bounding box in 'domain'.

    The number of variables max(1, N*Q), where
    - N is the number of continuous variables of the 'domain'.
    - Q is 'qhardness', a parameter in [0, 1]

    If 'support' is not None, ensures the satisfiability of the generated queries.
    """
    queries = []
    i = 0
    np.random.seed(seed)
    while i < nqueries:
        bbox = [domain.var_domains[v] for v in domain.real_vars]
        nvars = len(bbox)
        p = np.array([np.random.uniform(l, u) for l, u in bbox])
        # uniformly sampled orientation for the hyperplane
        o = np.random.uniform(0, 1, (nvars - 1, nvars))
        # coefficients for the system of equations (i.e. n points in ndimensions)
        Points = p * np.concatenate((np.ones((1, nvars)), o))

        # solving the system to retrieve the hyperplane's coefficients
        # [p1 ; ... , pn] * coeffs = 1
        w = solve_linear_system(Points, np.ones((nvars, 1))).transpose()[0]

        # consider a subset maybe?
        selected = np.random.choice(nvars, int(nvars * qhardness), replace=False)
        if len(selected) == 0:
            selected = [np.random.choice(nvars)]

        wx = [Times(Real(float(w[j])), x)
              for j, x in enumerate(domain.get_real_symbols())
              if j in selected]
        query = LE(Plus(*wx), Real(1))

        if support is None or is_sat(And(support, query)):
            queries.append(query)
            i += 1
        else:
            print(f"UNSAT {i + 1}/{nqueries}")

    return queries
