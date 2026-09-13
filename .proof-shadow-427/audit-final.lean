import EdensConjecture.EStatement

#print axioms Eden.EdensConjecture_False
#print axioms Eden.EdensConjectureNeedNotUnstable_False
#print axioms Eden.EdensConjectureQuestion1_False

example : ¬ Eden.EdensConjecture := Eden.EdensConjecture_False
example : ¬ Eden.EdensConjectureNeedNotUnstable.{0} := Eden.EdensConjectureNeedNotUnstable_False
example : ¬ Eden.EdensConjectureNeedNotUnstable.{1} := Eden.EdensConjectureNeedNotUnstable_False
example : ¬ Eden.EdensConjectureQuestion1.{0} := Eden.EdensConjectureQuestion1_False
example : ¬ Eden.EdensConjectureQuestion1.{1} := Eden.EdensConjectureQuestion1_False
