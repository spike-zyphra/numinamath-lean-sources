import Mathlib

theorem number_theory_252531 (a : Fin 10 → ℕ) (ha : a = fun n => match n with
    | 0 => 1 | 1 => 4 | 2 => 8 | 3 => 10 | 4 => 16 | 5 => 19 | 6 => 21 | 7 => 25 | 8 => 30 | 9 => 43) :
    {(i, j) : Fin 10 × Fin 10 | i ≤ j ∧ 11 ∣ ∑ k in Finset.Icc i j, a k}.ncard = 7 := by
  rw [Set.ncard_eq_toFinset_card']
  simp [ha, Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top]
  <;> native_decide