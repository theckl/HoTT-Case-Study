import sets.basic

universes u u' v w
hott_theory

namespace hott

namespace set

/- We construct finite sets of arbitrary size using the sum of sets in the induction step. -/
@[hott]
def fin_Set (n : ℕ) : Set.{0} :=
begin hinduction n with n fin_n, exact Zero_Set, exact sum_Set fin_n One_Set end  

end set

end hott