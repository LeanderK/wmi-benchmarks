import os
from sys import argv

from wmibench.uci_det.det import DET
from wmibench.data.synthetic import generate_random_queries
from wmibench.data.uci import generate_uci_loop
from wmibench.io import Density


def generate_benchmark(nmin, nmax, nqueries, qhardness, root_folder, seed):
    def uci_to_pywmi(feats, train, valid):
        det = DET(feats, nmin, nmax)
        det.grow_full_tree(train)
        det.prune_with_validation(valid)

        domain, support, weight = det.to_pywmi()
        queries = generate_random_queries(domain, nqueries, qhardness, seed,
                                          support=support)
        density = Density(support, weight, queries, domain=domain)
        return density, det.size()

    if not os.path.isdir(root_folder):
        os.mkdir(root_folder)

    generate_uci_loop(root_folder, uci_to_pywmi)


if __name__ == '__main__':
    if len(argv) != 6:
        print("Usage: python3 uci_det.py N_MIN N_MAX NQUERIES QUERYHARDNESS SEED")
        exit(1)

    nmin = int(argv[1])
    nmax = int(argv[2])
    nqueries = int(argv[3])
    qhardness = float(argv[4])
    seed = int(argv[5])
    exp_str = f'uci-det-m:{nmin}-M:{nmax}-N:{nqueries}-Q:{qhardness}-S:{seed}'
    root_folder = os.path.join(os.getcwd(), exp_str)
    generate_benchmark(nmin, nmax, nqueries, qhardness, root_folder, seed)
