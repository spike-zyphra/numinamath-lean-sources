import Mathlib

def isSparkly (n : ℕ) := n.minFac = n.divisors.card

/- determine -/ abbrev solution : ℕ := 3

theorem number_theory_188695 :
    Set.ncard {n | 2 ≤ n ∧ n ≤ 2003 ∧ isSparkly n} = solution := by
  have h1 : {n | 2 ≤ n ∧ n ≤ 2003 ∧ isSparkly n} = 
          Finset.filter (λ n => 2 ≤ n ∧ n ≤ 2003 ∧ n.minFac = n.divisors.card) (Finset.Icc 0 2003) := by
    ext n
    simp [isSparkly]
    <;> try { tauto }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide