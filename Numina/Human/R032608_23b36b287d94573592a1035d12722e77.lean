import Mathlib

theorem algebra_96407 (a : Fin 5 → ℕ) (ha : ∑ i, a i = 5 * 30) (h : 18 ∈ Set.range a) :
    (5 - 1) * 33 = ∑ i, a i - 18 := by 
  simp_all [Finset.mem_range]
  <;> omega