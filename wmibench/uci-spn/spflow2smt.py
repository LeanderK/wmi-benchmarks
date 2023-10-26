
import numpy as np
from pysmt.shortcuts import And, BOOL, Exp, LE, Ite, Minus, Or, Plus, Pow, REAL,\
    Real, Symbol, Times
from pywmi import Domain
from spn.structure.leaves.parametric.Parametric import Categorical, Gaussian
from spn.structure.Base import Context
from spn.structure.Base import Product as SPNProduct
from spn.structure.Base import Sum as SPNSum

def get_context_from_dataset(feats, train):
    types = [Categorical if f.symbol_type() == BOOL  else Gaussian
             for f in feats]
    return Context(parametric_types=types).add_domains(train)

def spn_size(spn):
    if isinstance(spn, SPNSum) or isinstance(spn, SPNProduct):
        return 1 + sum([spn_size(c) for c in spn.children])
    else:
        return 0
 

def spn_to_weight(spn, smtvars):
    ''' Converts an SPN in SPFlow into a weight function in pysmt.

    Currently only works with Gaussian and (binary) Categorical types.

    '''
    if isinstance(spn, SPNSum):
        assert(np.isclose(np.sum(spn.weights), 1.0))
        wsum = [Times(Real(float(spn.weights[i])),
                      spn_to_weight(spn.children[i], smtvars))
                for i in range(len(spn.children))]
        return Plus(*wsum)

    elif isinstance(spn, SPNProduct):
        return Times(*[spn_to_weight(c, smtvars) for c in spn.children])

    elif isinstance(spn, Categorical):
        assert(len(spn.p) <= 2)
        assert(np.isclose(np.sum(spn.p), 1.0))
        welse = float(spn.p[0]) if len(spn.p) == 2 else 0.0
        return Ite(smtvars[spn.scope[0]],
                   Real(float(spn.p[-1])),
                   Real(welse))

    elif isinstance(spn, Gaussian):
        return Times(Real(float(1/np.sqrt(spn.variance*2*np.pi))),
                     Exp(Times(Real(float(-1/(2*spn.variance))),
                               Pow(Minus(smtvars[spn.scope[0]],
                                         Real(float(spn.mean))),
                                   Real(2)))))
    else:
        raise NotImplementedError(f"Unsupported node: {type(spn)}")


def convert(context, spn):
    assert(spn.scope == list(range(len(spn.scope))))
    smtvars = []
    bvars = []
    cvars = []
    cbounds = []
    clauses = []
    for i in range(len(spn.scope)):
        ptype = context.get_parametric_types_by_scope([i])[0]
        if ptype == Categorical:
            v = Symbol(f'a{i}', BOOL)
            bvars.append(v.symbol_name())
            
        elif ptype == Gaussian:
            v = Symbol(f'x{i}', REAL)
            cvars.append(v.symbol_name())
            l, u = context.get_domains_by_scope([i])[0]
            clauses.append(And(LE(Real(float(l)), v), LE(v, Real(float(u)))))
            cbounds.append((l, u))
            
        else:
            raise NotImplementedError(f"Unsupported type: {ptype}")

        smtvars.append(v)

    support = And(*clauses)
    weight = spn_to_weight(spn, smtvars)
    domain = Domain.make(bvars, cvars, cbounds)
    size = spn_size(spn)

    return support, weight, domain, size
