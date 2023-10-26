
from det import DET
import numpy as np
import os
from pysmt.shortcuts import *
from pywmi import Density
from scipy.linalg import solve as solve_linear_system
from sys import argv
from utils import read_feats, read_data



# full MLC suite sorted by increasing number of features
EXPERIMENTS = {'small' : ['balance-scale', 'iris', 'cars', 'diabetes', 'breast-cancer',
                          'glass2', 'glass', 'breast', 'solar', 'cleve', 'hepatitis'],
               'big' : ['heart', 'australian', 'crx', 'german', 'german-org', 'auto',
                        'anneal-U']}

DATAFOLDER = '../data/mlc-datasets'



if len(argv) != 6:
    print("Usage: python3 generate_dets.py N_MIN N_MAX NQUERIES QUERYHARDNESS SEED")
    exit(1)

nmin, nmax, nqueries, qhardness, seed = int(argv[1]), int(argv[2]), int(argv[3]), float(argv[4]), int(argv[5])

rows = ['\\hline', 'Dataset & $|\\allA|$ & $|\\allX|$ & \\# Train & \\# Valid\\\\', '\\hline']
for size in EXPERIMENTS:
    benchmark_folder = f'dets-{size}-{nmin}-{nmax}-{nqueries}-{qhardness}-{seed}'

    if not os.path.isdir(benchmark_folder):
        os.mkdir(benchmark_folder)

    for exp in EXPERIMENTS[size]:
        # fresh pysmt environment
        reset_env()
    
        detfile = os.path.join(benchmark_folder, f'{exp}-{nmin}-{nmax}.json')

        if os.path.isfile(detfile):
            print(f"{detfile} exists. Skipping.")
            continue

        print(f"{exp} : Parsing data")    
        featfile = os.path.join(DATAFOLDER, f'{exp}.features')
        feats = read_feats(featfile)
        train = read_data(os.path.join(DATAFOLDER, f'{exp}.train.data'), feats)
        valid = read_data(os.path.join(DATAFOLDER, f'{exp}.valid.data'), feats)

        nbools = len([v for v in feats if v.symbol_type() == BOOL])
        nreals = len([v for v in feats if v.symbol_type() == REAL])
        rows.append(f'{exp} & {nbools} & {nreals} & {len(train)} & {len(valid)} \\\\')



        print(f"{exp} : Learning DET({nmin},{nmax})")
        det = DET(feats, nmin, nmax)
        det.grow_full_tree(train)
        det.prune_with_validation(valid)

        domain, support, weight = det.to_pywmi()
        queries = []
        i = 0
        #for i in range(nqueries):
        np.random.seed(seed)
        while i < nqueries:
            bbox = [domain.var_domains[v] for v in domain.real_vars]
            nvars = len(bbox)
            p = np.array([np.random.uniform(l, u) for l, u in bbox])
            # uniformly sampled orientation for the hyperplane
            o = np.random.uniform(0, 1, (nvars-1, nvars))
            # coefficients for the system of equations (i.e. n points in ndimensions)
            Points = p * np.concatenate((np.ones((1, nvars)), o))

            # solving the system to retrieve the hyperplane's coefficients
            # [p1 ; ... , pn] * coeffs = 1
            w = solve_linear_system(Points, np.ones((nvars, 1))).transpose()[0]

            # consider a subset maybe?
            selected = np.random.choice(nvars, int(nvars*qhardness), replace=False)
            if len(selected) == 0:
                selected = [np.random.choice(nvars)]

            wx = [Times(Real(float(w[j])), x)
                  for j,x in enumerate(domain.get_real_symbols())
                  if j in selected]
            query = LE(Plus(*wx), Real(1))

            if is_sat(And(support, query)):
                queries.append(query)
                i += 1
            else:
                print(f"UNSAT {i+1}/{nqueries}")
            
        density = Density(domain, support, weight, queries)
        density.to_file(detfile)  # Save to file
        # density = Density.from_file(filename)  # Load from file

with open('table.tex', 'w') as f:
    f.write('\n'.join(rows))



                    

    
