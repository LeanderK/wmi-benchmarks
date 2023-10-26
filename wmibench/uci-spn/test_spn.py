
import numpy as np
from pysmt.shortcuts import *
from spflow2smt import convert
from spn.algorithms.LearningWrappers import learn_parametric
from spn.structure.Base import Context
from spn.structure.leaves.parametric.Parametric import Categorical, Gaussian

from wmipa import WMI
from wmipa.integration import VolestiIntegrator


np.random.seed(123)

a = np.random.randint(2, size=1000).reshape(-1, 1)
b = np.random.randint(2, size=1000).reshape(-1, 1)
x = np.r_[np.random.normal(10, 5, (300, 1)), np.random.normal(20, 10, (700, 1))]
y = 5 * a + 3 * b + x
train_data = np.c_[a, b, x, y]

context = Context(parametric_types=[Categorical, Categorical, Gaussian, Gaussian]).add_domains(train_data)
spn = learn_parametric(train_data, context, min_instances_slice=20)

support, weight, domain = convert(context, spn)

solver = WMI(support, weight, integrator=VolestiIntegrator)
from pysmt.shortcuts import Bool
print(solver.computeWMI(Bool(True)))
