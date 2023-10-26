
# wmibench

This is `wmibench`, a collection of benchmarks for *PROBABILISTIC INFERENCE with
**algebraic** and **logical*** constraints, implemented in Python 3.

- The hybrid logical/algebraic constraints are encoded as
[Satisfiability Modulo Theories
(SMT)](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories)
formulas over Boolean and continuous variables.
- Densities are
either piecewise polynomials or Gaussians.

The format is based on `pywmi`
([GitHub](https://github.com/weighted-model-integration/pywmi)).

The goal of this package is providing a unified library for testing
pywmi-compatible [Weighted Model
Integration](http://web.cs.ucla.edu/~guyvdb/papers/BelleIJCAI15.pdf)
[Belle et al. 2015] algorithms.

## Synthetic benchmarks

A number of algorithms for generating synthetic benchmarks are included.

### Randomized

Randomized weighted SMT formulas from "Efficient WMI via SMT-Based Predicate Abstraction" [Morettin et al. 2017] ([pdf](https://www.ijcai.org/proceedings/2017/0100.pdf)) and follow-up works.

Run:

`python3 synthetic/synthetic_pa.py [-h] [-o OUTPUT] [-r REALS] [-b BOOLEANS] [-d DEPTH] [-m MODELS] [-s SEED]`

### Structured

Synthetic problems from the following classes:

1- Kolb et al., 2019 ([pdf](http://proceedings.mlr.press/v115/kolb20a/kolb20a.pdf));
2- Zeng et al., 2020 ([pdf](http://proceedings.mlr.press/v115/zeng20a/zeng20a.pdf)).

Run:

`python3 synthetic/synthetic_structured.py [-h] [-s SEED] [--output_folder OUTPUT_FOLDER] class size`

with `class` in:

- xor [1]
- mutex [1]
- click [1]
- uni [1]
- dual [1]
- dual_paths [1]
- dual_paths_distinct [1]
- and_overlap [1]
- tpg_star [2]
- tpg_3ary_tree [2]
- tpg_path [2]


## Answering random algebraic queries on ML models

The following benchmarks test the capabilities of answering random
oblique queries of the form:

$Pr(w X \le b)$ with $w \in \mathbb{R}^k, b \in \mathbb{R}$

on probabilistic models learned from data.

Specifically, the models are trained on (a selection of) [UCI
datasets](https://archive.ics.uci.edu/ml/index.php) having both
continuous and discrete features. These datasets are included in
`data/uci-datasets`.


### Density Estimation Trees

The paper ["SMT-based weighted model integration with structure
awareness"](https://proceedings.mlr.press/v180/spallitta22a/spallitta22a.pdf)
(Spallitta et al., 2022) first featured experiments where
probabilities of oblique queries are computed on ["Density Estimation
Trees"](https://dl.acm.org/doi/pdf/10.1145/2020408.2020507) (Ram and
Grey, 2011).

To generate the benchmarks, run:

`python3 uci-det/uci-det.py N_MIN N_MAX NQUERIES QUERYHARDNESS SEED`

where:

- `NMIN` and `NMAX` are hyperparameters of the greedy DET learning algorithm;
- `NQUERIES` and `QUERYHARDNESS` respectively control how many queries are generated and the ratio of variables involved in them;
- `SEED` sets the seed number of the pseudo-random number generator.


### Sum-Product Networks

Sum-Product Networks (see e.g. ["Sum-product networks: A new deep
architecture"](https://ieeexplore.ieee.org/iel5/6114268/6130192/06130310.pdf)
(Poon and Domingos, 2011)) with Gaussian and Categorical leaves are also considered.

These benchmarks additionally require the `SPFlow` library
([GitHub](https://github.com/SPFlow/SPFlow)).

Run:

`python3 uci-spn/uci-spn.py MIN_INST_SLICE NQUERIES QUERYHARDNESS SEED`

where:

- `MIN_INST_SLICE` is an hyperparameter of the greedy SPN learning algorithm;
- `NQUERIES` and `QUERYHARDNESS` respectively control how many queries are generated and the ratio of variables involved in them;
- `SEED` sets the seed number of the pseudo-random number generator.


## Fairness of probabilistic programs

TODO