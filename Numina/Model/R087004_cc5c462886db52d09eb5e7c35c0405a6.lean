import Mathlib

theorem number_theory_158471 (a : Fin 5 → ℕ) (ha : ∀ i, a i > 0)
    (hinc : ∀ i j, i < j → a i < a j) (hsum : ∑ i, a i = 2022) :
    a 0 + a 1 + a 2 ≤ 1209 := by
  have h1 : a 0 < a 1 := hinc 0 1 (by simp)
  have h2 : a 1 < a 2 := hinc 1 2 (by simp)
  have h3 : a 2 < a 3 := hinc 2 3 (by simp)
  have h4 : a 3 < a 4 := hinc 3 4 (by simp)
  have h0_pos : a 0 > 0 := ha 0
  have h1_pos : a 1 > 0 := ha 1
  have h2_pos : a 2 > 0 := ha 2
  have h3_pos : a 3 > 0 := ha 3
  have h4_pos : a 4 > 0 := ha 4
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum
  omega