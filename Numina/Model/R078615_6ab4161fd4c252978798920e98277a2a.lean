import Mathlib

def is_multiplicatively_perfect (n : ℕ) : Prop :=
  ∏ d in n.divisors, d = n ^ 2

theorem number_theory_68478 :
    Set.ncard {n | n < 100 ∧ is_multiplicatively_perfect n} = 33 := by
  have h1 : {n | n < 100 ∧ is_multiplicatively_perfect n} = (Finset.Iio (100 : ℕ)).filter (fun n => ∏ d in n.divisors, d = n ^ 2) := by
    ext n
    simp [is_multiplicatively_perfect]
    <;> try { tauto }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide