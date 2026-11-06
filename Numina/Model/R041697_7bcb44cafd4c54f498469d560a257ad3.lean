import Mathlib

theorem number_theory_10482 (a : Fin 10 → ℕ) (ha : a = ![1, 4, 8, 10, 16, 19, 21, 25, 30, 43]) :
    {(i, j) : Fin 10 × Fin 10 | i ≤ j ∧ 11 ∣ ∑ k in Finset.Icc i j, a k}.ncard = 7 := by
  rw [ha]
  simp [Set.ncard_eq_toFinset_card']
  <;> native_decide