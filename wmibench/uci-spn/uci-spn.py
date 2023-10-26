

import os
from pywmi import Density
from spflow2smt import convert, get_context_from_dataset
from spn.algorithms.LearningWrappers import learn_parametric
from spn.structure.Base import Context
from spn.structure.leaves.parametric.Parametric import Categorical, Gaussian
from sys import argv

from wmibench.data.synthetic import generate_random_queries
from wmibench.data.uci import generate_uci_loop

def generate(min_instances_slice, nqueries, qhardness, root_folder, seed):

    def uci_to_pywmi(feats, train, valid):
        context = get_context_from_dataset(feats, train)        
        spn = learn_parametric(train, context, min_instances_slice=min_instances_slice)
        
        support, weight, domain, size = convert(context, spn)
        queries = generate_random_queries(domain, nqueries, qhardness, seed,
                                          support=support)            
        density = Density(domain, support, weight, queries)
        return density, size

    if not os.path.isdir(root_folder):
        os.mkdir(root_folder)

    generate_uci_loop(root_folder, uci_to_pywmi)


if __name__ == '__main__':
    if len(argv) != 5:
        print("Usage: python3 uci_spn.py MIN_INSTANCES_SLICE NQUERIES QUERYHARDNESS SEED")
        exit(1)

    min_instances_slice = int(argv[1])
    nqueries = int(argv[2])
    qhardness = float(argv[3])
    seed = int(argv[4])
    exp_str = f'uci-spn-mis:{min_instances_slice}-N:{nqueries}-Q:{qhardness}-S:{seed}'
    root_folder = os.path.join(os.getcwd(), exp_str)
    generate(min_instances_slice, nqueries, qhardness, root_folder, seed)
