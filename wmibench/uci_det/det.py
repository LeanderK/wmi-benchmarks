import math
from copy import copy
from math import fsum

import numpy as np
from pysmt.shortcuts import And, BOOL, LE, Ite, Not, REAL, Real

LOG_ZERO = 1e-3


class Node:

    def __init__(self, manager, parent, train, bounds):
        assert (manager.n_min < manager.n_max), "NMIN >= NMAX"
        assert (len(train) >= manager.n_min), "|DATA| < NMIN"
        self.manager = manager
        self.parent = parent
        self.bounds = bounds
        self.volume = Node.compute_volume(self.bounds)
        self.n_node = len(train)
        self.weight = float(self.n_node) / (self.manager.n_tot * self.volume)
        self.data = train
        self.error = Node.compute_node_error(manager.n_tot, self.n_node, self.bounds)
        self.marked = False

        if self.n_node <= manager.n_max:
            self.turn_into_leaf()
        else:
            tentative_split = self.split(train)

            if tentative_split is None:
                self.turn_into_leaf()

            else:
                best, pos_train, neg_train, pos_bounds, neg_bounds = tentative_split

                self.split_idx, self.split_value = best
                self.pos = Node(manager, self, pos_train, pos_bounds)
                self.neg = Node(manager, self, neg_train, neg_bounds)

        if not self.is_leaf():
            pw, pv = self.pos.weight, self.pos.volume
            nw, nv = self.neg.weight, self.neg.volume
            assert (np.isclose(self.weight * self.volume,
                               (pw * pv) + (nw * nv))), "Invariant"
            assert (self.volume > self.neg.volume), "Volume should decrease"
            assert (self.volume > self.pos.volume), "Volume should decrease"

    def compute_split_score(self, n_pos, n_neg, pos_bounds, neg_bounds):
        n_tot = self.manager.n_tot

        return self.error \
            - Node.compute_node_error(n_tot, n_pos, pos_bounds) \
            - Node.compute_node_error(n_tot, n_neg, neg_bounds)

    def copynode(self):
        copy_node = copy(self)
        if not copy_node.is_leaf():
            copy_node.pos = copy_node.pos.copynode()
            copy_node.neg = copy_node.neg.copynode()

        return copy_node

    def get_density(self, point):
        assert (len(point) == len(self.manager.feats))

        if self.is_outside_bounds(point):
            return 0.0

        elif self.is_leaf():
            return self.weight

        else:
            split_var = self.manager.feats[self.split_idx]
            if split_var.symbol_type() == REAL:
                if point[self.split_idx] <= self.split_value:
                    return self.pos.get_density(point)
                else:
                    return self.neg.get_density(point)
            else:
                if point[self.split_idx]:
                    return self.pos.get_density(point)
                else:
                    return self.neg.get_density(point)

    def get_leaves(self):
        if self.is_leaf():
            return [self]
        else:
            return self.pos.get_leaves() + self.neg.get_leaves()

    def merge_marked(self):
        assert (not self.marked), "Shouldn't be marked"
        if not self.is_leaf():
            assert (not (self.pos.marked and self.neg.marked)), "Children shouldn't be both marked"
            if self.pos.marked or self.neg.marked:
                self.turn_into_leaf()
            else:
                self.pos.merge_marked()
                self.neg.merge_marked()

    def get_internal_nodes(self):
        if self.is_leaf():
            return []
        else:
            return [self] + self.pos.get_internal_nodes() + self.neg.get_internal_nodes()

    def is_boolean_split(self):
        return (not self.is_leaf()) and \
            self.manager.feats[self.split_idx].symbol_type() == BOOL

    def is_continuous_split(self):
        return (not self.is_leaf()) and \
            self.manager.feats[self.split_idx].symbol_type() == REAL

    def is_leaf(self):
        return (self.pos == None and self.neg == None)

    def is_outside_bounds(self, point):
        assert (len(point) == len(self.bounds)), "Dimension mismatch"
        for i, val in enumerate(point):
            var = self.manager.feats[i]
            if var.symbol_type() == REAL:
                if val < self.bounds[var][0] or val > self.bounds[var][1]:
                    return True

            elif var.symbol_type() == BOOL:
                if self.bounds[var] is not None and self.bounds[var] != val:
                    return True

        return False

    def pretty_print(self):
        nodestr = "({} {} {} {})"
        if self.is_leaf():
            nodetype = "L {}".format(str(self.weight))
        else:
            split_var = self.manager.feats[self.split_idx]
            varName = split_var.symbol_name()
            if split_var.symbol_type() == BOOL:
                condition = varName
            else:
                condition = "({} <= {})".format(varName,
                                                str(float(self.split_value)))

            nodetype = "C {}\n{}\n{}".format(condition, self.pos.pretty_print(),
                                             self.neg.pretty_print())
        return nodestr.format(self.bounds, self.weight, self.volume, nodetype)

    def split(self, train):
        assert (len(train) > 1), "Can't split a single instance"
        best_score = None

        for idx, var in enumerate(self.manager.feats):

            if var.symbol_type() == REAL:
                # TODO: this doesn't need to be done at each iteration
                values = sorted(list({row[idx] for row in train}))

                for i in range(len(values) - 1):
                    split_val = (values[i] + values[i + 1]) / 2.0
                    pos = train[train[:, idx] <= split_val]
                    neg = train[train[:, idx] > split_val]

                    if len(pos) < self.manager.n_min or len(neg) < self.manager.n_min:
                        continue

                    posB, negB = Node.compute_split_bounds(self.bounds,
                                                           var, split_val)

                    score = self.compute_split_score(len(pos), len(neg),
                                                     posB, negB)
                    if best_score is None or best_score < score:
                        best_score = score
                        best_split = (idx, split_val)
                        pos_train = pos
                        neg_train = neg
                        pos_bounds = posB
                        neg_bounds = negB

            elif var.symbol_type() == BOOL:
                split_val = True
                pos = train[train[:, idx] == 1]
                neg = train[train[:, idx] == 0]

                if len(pos) < self.manager.n_min or len(neg) < self.manager.n_min:
                    continue

                posB, negB = Node.compute_split_bounds(self.bounds, var, split_val)
                score = self.compute_split_score(len(pos), len(neg), posB, negB)
                if best_score is None or best_score < score:
                    best_score = score
                    best_split = (idx, True)
                    pos_train = pos
                    neg_train = neg
                    pos_bounds = posB
                    neg_bounds = negB

            else:
                assert (False), "Unsupported variable type."

        if not best_score is None:
            return best_split, pos_train, neg_train, pos_bounds, neg_bounds

    def turn_into_leaf(self):
        self.pos = None
        self.neg = None

    '''
    @property
    def weight(self):
        return float(self.n_node) / (self.manager.n_tot * self.volume)
    '''

    def bounds2domain(self):
        domain = dict()
        for var in self.bounds:
            if var.symbol_type() == REAL:
                vbounds = list(self.bounds[var])
            else:
                vbounds = None

            domain[var] = vbounds

        return domain

    def bounds2smt(self):
        formula = []
        for var in self.bounds:
            if var.symbol_type() == REAL:
                lower, upper = self.bounds[var]
                formula.append(And(LE(Real(float(lower)), var),
                                   LE(var, Real(float(upper)))))

            elif self.bounds[var] is not None:
                bool_bound = var if self.bounds[var] else Not(var)
                formula.append(bool_bound)

        return And(formula)

    def weight2smt(self):
        if self.is_leaf():
            return Real(float(self.weight))
        else:
            var = self.manager.feats[self.split_idx]
            if var.symbol_type() == BOOL:
                condition = var
            else:
                condition = LE(var, Real(float(self.split_value)))

            return Ite(condition,
                       self.pos.weight2smt(),
                       self.neg.weight2smt())

    @staticmethod
    def compute_node_error(n_tot, n_node, bounds):
        volume = Node.compute_volume(bounds)
        return -(pow(n_node, 2) / (pow(n_tot, 2) * volume))

    @staticmethod
    def compute_split_bounds(bounds, split_var, split_value):
        pos_bounds, neg_bounds = dict(), dict()
        for var in bounds:
            varbounds = bounds[var]
            if var.symbol_type() == REAL:
                assert (varbounds is not None), "Continuous bounds can't be None"
                assert (len(varbounds) == 2), "Continuous bounds should have len 2"
                pos_bounds[var] = list(varbounds)
                neg_bounds[var] = list(varbounds)
            elif varbounds is not None:
                pos_bounds[var] = varbounds
                neg_bounds[var] = varbounds
            else:
                pos_bounds[var] = None
                neg_bounds[var] = None

        if split_var.symbol_type() == REAL:
            pos_bounds[split_var][1] = split_value
            neg_bounds[split_var][0] = split_value
        else:
            assert (bounds[split_var] is None), "Boolean split must be unassigned"
            pos_bounds[split_var] = split_value
            neg_bounds[split_var] = not split_value

        return pos_bounds, neg_bounds

    @staticmethod
    def compute_volume(bounds):
        assert (len(bounds) > 0), "Can't compute volume with no bounds"
        volume = 1
        for var in bounds:
            if var.symbol_type() == REAL:
                lower, upper = bounds[var]
                volume = volume * (upper - lower)
            else:
                if bounds[var] is None:
                    volume = volume * 2

        assert (volume > 0), "Volume must be positive"
        return volume


class DET:

    def __init__(self, feats, n_min=5, n_max=10):
        self.feats = feats
        self.n_min = n_min
        self.n_max = n_max
        self.root = None

    def grow_full_tree(self, train):
        self.n_tot = len(train)
        initialBounds = DET.compute_initial_bounds(self.feats, train)
        self.root = Node(self, None, train, initialBounds)

    def prune_with_cv(self, train, n_bins=10):
        # keep pruning the trees while possible
        # compute a finite set of alpha values
        assert (n_bins > 0 and n_bins <= len(train))
        trees = [(self.root, 0.0)]
        while not trees[-1][0].is_leaf():
            nextTree = trees[-1][0].copynode()
            minAlpha = None
            for t in nextTree.get_internal_nodes():
                alpha = DET.g(t)
                if minAlpha == None or alpha < minAlpha:
                    minAlpha = alpha
                    minT = t

            minT.turn_into_leaf()
            trees.append((nextTree, minAlpha))

        cvTrees = []
        cv_bins = []
        bin_size = int(math.ceil(len(train) / float(n_bins)))
        for i in range(n_bins):
            imin = i * bin_size
            imax = (i + 1) * bin_size
            btrain = np.concatenate((train[:imin], train[imax:]))
            bvalid = train[imin:imax]

            assert (len(btrain) + len(bvalid) == len(train))
            cv_bins.append((btrain, bvalid))

        return cv_bins
        for i, cv_bin in enumerate(cv_bins):
            iTrain = cv_bin[0]
            iBounds = DET.compute_initial_bounds(self.feats, iTrain)
            iTree = Node(self, None, len(iTrain), iTrain, iBounds)
            cvTrees.append(iTree)

        for i, cvTree in enumerate(cvTrees):
            validation = cv_bins[i][1]
            alpha_cv_tree = cvTree.copynode()

            for t in range(len(trees) - 2):
                cvReg = 0.0
                for row in validation:
                    # datapoint = {self.feats[j] : row[j] for j in range(len(row))}
                    # cvReg += alpha_cv_tree.get_density(datapoint)
                    cvReg += alpha_cv_tree.get_density(row)

                regularization[t] += 2.0 * cvReg / self.N

                est_alpha = 0.5 * (trees[t + 1][1] + trees[t + 2][1])
                # DET.prune_tree(alpha_cv_tree, est_alpha)
                for t in alpha_cv_tree.get_internal_nodes():
                    if DET.g(t) <= est_alpha:
                        t.turn_into_leaf()

            cvReg = 0.0
            for row in validation:
                # datapoint = {self.feats[j] : row[j] for j in range(len(row))}
                # cvReg += alpha_cv_tree.get_density(datapoint)
                cvReg += alpha_cv_tree.get_density(row)

            regularization[len(trees) - 2] += 2.0 * cvReg / self.N

        maxError = None
        for t in range(len(trees) - 1):
            alpha_tree, alpha = trees[t]
            r_alpha_tree = DET.compute_tree_error(alpha_tree)
            error = regularization[t] + r_alpha_tree

            if maxError == None or error > maxError:
                maxError = error
                self.root = alpha_tree

    def prune_with_validation(self, validation, epsilon=None):

        if epsilon is None:
            epsilon = LOG_ZERO
        # keep pruning the trees while possible
        # compute a finite set of alpha values
        trees = [(self.root, 0.0)]
        while not trees[-1][0].is_leaf():
            nextTree = trees[-1][0].copynode()
            minAlpha = None
            for t in nextTree.get_internal_nodes():
                alpha = DET.g(t)
                if minAlpha == None or alpha < minAlpha:
                    minAlpha = alpha
                    minT = t

            minT.turn_into_leaf()
            trees.append((nextTree, minAlpha))

        max_likelihood = None
        for alpha_tree, alpha in trees:
            # compute log-likelihood of the validation set
            log_l = 0
            for row in validation:
                # datapoint = {self.feats[j] : row[j] for j in range(len(row))}
                # density = alpha_tree.get_density(datapoint)
                density = alpha_tree.get_density(row)
                log_l += np.log(density) if density else epsilon

            if max_likelihood is None or log_l > max_likelihood:
                max_likelihood = log_l
                self.root = alpha_tree

    @staticmethod
    def copy(det):
        copiedDET = DET(det.feats, det.n_min, det.n_max)
        copiedDET.root = det.root.copynode()
        return copiedDET

    @staticmethod
    def compute_initial_bounds(feats, train):
        bounds = {}
        for idx, var in enumerate(feats):
            if var.symbol_type() == REAL:
                lower = None
                upper = None
                for row in train:
                    if lower is None or row[idx] < lower:
                        lower = row[idx]
                    if upper is None or row[idx] > upper:
                        upper = row[idx]

                bounds[var] = [lower, upper]

            elif var.symbol_type() == BOOL:
                vals = {row[idx] for row in train}
                if len(vals) == 2:
                    bounds[var] = None
                else:
                    assert (len(vals) == 1), "More than 2 Boolean values"
                    bounds[var] = list(vals)[0]

        return bounds

    def to_pywmi(self):
        domain = self.root.bounds2domain()
        support = self.root.bounds2smt()
        weight = self.root.weight2smt()
        return domain, support, weight

    def size(self):
        return len(self.root.get_internal_nodes())

    @staticmethod
    def compute_tree_error(tree):
        return fsum([l.error for l in tree.get_leaves()])

    @staticmethod
    def g(node):
        return (node.error - DET.compute_tree_error(node)) / (len(
            node.get_leaves()) - 1.0)


if __name__ == '__main__':
    from pysmt.shortcuts import Symbol

    np.random.seed(8)

    n_vars = 2
    mix = [1 / 10 for _ in range(10)]
    populations = []
    train_size = 900
    valid_size = 100
    test_size = 100
    for m, w in enumerate(mix):
        mean = [m * 10] * n_vars
        # mean = [0]*n_vars
        variance = [np.random.random() * 10 for _ in range(n_vars)]
        print(f"Mixture {m}: \nWeight:{w} \nMean: {mean}\nVariance:{variance}\n")
        populations.append(np.random.normal(mean, variance,
                                            size=(train_size + valid_size + test_size, n_vars)))

    data = np.array([populations[np.random.choice(len(mix), p=mix)][i]
                     for i in range(len(populations[0]))])

    train = data[: train_size]
    valid = data[train_size: train_size + valid_size]
    test = data[train_size + valid_size:]

    n_min, n_max = 5, 10
    feats = [Symbol(f'x{i}', REAL) for i in range(n_vars)]
    det = DET(feats, n_min, n_max)
    det.grow_full_tree(train)
    det.prune_with_validation(valid)

    domain, support, weight = det.to_pywmi()
