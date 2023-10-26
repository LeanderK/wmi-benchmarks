
A collection of benchmarks for *PROBABILISTIC INFERENCE* 
with **algebraic** and **logical** constraints.

## Structure-aware WMI-PA @ UAI22

The paper features experiments where Density Estimation Trees (DETs) are trained on [UCI data](https://archive.ics.uci.edu/ml/index.php) (in `data/mlc-datasets`). A number of queries over the continuous variable models are generated:

$Pr(w X \le b)$ with $w \in \mathbb{R}^k, b \in \mathbb{R}$

Go to `uai-22/` and run:

`python3 generate_dets.py N_MIN N_MAX NQUERIES QUERYHARDNESS SEED`

where:

- `NMIN` and `NMAX` are hyperparameters of the greedy DET learning algorithm. They constrain the min. and max. number of instances in the leaves of the DET
- `NQUERIES` and `QUERYHARDNESS` respectively control how many queries over the learned models are generated and the ratio of variables involved in the query.
- `SEED` sets a seed number
