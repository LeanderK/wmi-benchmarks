
import numpy as np
from pysmt.shortcuts import BOOL, LE, Plus, REAL, Real, Symbol, Times, reset_env
from string import ascii_letters


def read_feats(path):
    feats = []
    with open(path, 'r') as f:
        for line in f:
            if len(line) == 0:
                continue

            tokens = line.strip()[:-1].split(':')
            assert(len(tokens) > 0), "Couldn't parse any token"

            feat_name = "".join(c for c in tokens[0] if c in ascii_letters + '0123456789')
            str_type = tokens[1]                
                
            if str_type == "continuous" or str_type == "discrete":
                feats.append(Symbol(feat_name, REAL))

            elif str_type == "categorical":
                nvals = len(tokens[2].split(","))
                if nvals == 2:
                    feats.append(Symbol(feat_name, BOOL))
                else:
                    for i in range(nvals):
                        feats.append(Symbol(f'{feat_name}_OHE_{i}', BOOL))
            else:
                print("Unsupported feature type: {str_type}")
                exit(1)

    return feats


def read_data(path, feats):
    data = []
    with open(path, 'r') as f:
        for line in f:
            if len(line) == 0:
                continue

            tokens = line[:-1].replace(' ','').split(',')                
            row = []
            i = 0
            for token in tokens:
                if 'OHE' not in feats[i].symbol_name():
                    if feats[i].symbol_type() == BOOL:
                        assert(token in ["0", "1"])
                        row.append(bool(int(token)))
                    else:
                        row.append(float(token))

                    i += 1

                else:
                    prefix = "_".join(
                        feats[i].symbol_name().split("_")[:-1])
                    cardinality = len([f for f in feats if prefix in
                                       f.symbol_name()])
                    assert(int(float(token)) < cardinality)
                    subrow = [False for _ in range(cardinality)]
                    subrow[int(float(token))] = True
                    row.extend(subrow)
                    i += cardinality

                data.append(row)

    return np.array(data)
