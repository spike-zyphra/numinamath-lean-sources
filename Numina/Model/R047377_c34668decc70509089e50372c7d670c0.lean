import Mathlib

theorem algebra_229515 (a : Fin 14 → ℕ) (ha : ∀ i, a i > 0)
    (hsum : ∑ i ∈ Finset.range 9, a i = 50) (hmiddle : ∀ i ∈ Finset.range 5, a i = a (i + 4) + a (i + 5) + a (i + 6) + a (i + 7))
    (htop : a 0 = a 1 + a 2 + a 3 + a 4) :
    a 0 ≤ 118 := by
  have eq1 := hmiddle 0 (by simp)
  have eq2 := hmiddle 1 (by simp)
  have eq3 := hmiddle 2 (by simp)
  have eq4 := hmiddle 3 (by simp)
  have eq5 := hmiddle 4 (by simp)

  simp [Finset.mem_range] at hsum eq1 eq2 eq3 eq4 eq5
  simp [Finset.sum_range_succ] at hsum ⊢
  all_goals
    omega