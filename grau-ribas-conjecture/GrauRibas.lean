import GrauRibas.CubeRoot
import GrauRibas.Spec

-- Headline results, stated for any sequence satisfying the literal OEIS recurrence.
#print axioms GrauRibas.Spec.grau_ribas_conjecture
#print axioms GrauRibas.Spec.rate
#print axioms GrauRibas.Spec.second_order
#print axioms GrauRibas.Spec.cubes
#print axioms GrauRibas.Spec.exists_solution

-- Supporting results about the concrete sequence `a`.
#print axioms GrauRibas.a_succ
#print axioms GrauRibas.grauRibas_asymptotic
#print axioms GrauRibas.ratio_bound
#print axioms GrauRibas.second_order_bound
#print axioms GrauRibas.cubes_are_powers_of_eight
#print axioms GrauRibas.entry_formula
#print axioms GrauRibas.entry_value
#print axioms GrauRibas.previous_lt
#print axioms GrauRibas.block_value
#print axioms GrauRibas.cbrt_on_block
