import Mathlib

theorem algebra_99358 (a b c : Fin 100 → ℝ) (ha : ∀ n, a n ≠ 0) :
    Set.ncard {x | ∃ y, y = a n * x ^ 2 + b n * x + c n} ≤ 10001 := by
  have h1 : {x | ∃ y, y = a n * x ^ 2 + b n * x + c n} = Set.univ := by
    ext x
    simp
  rw [h1]
  simp [Set.ncard_univ, Set.ncard_eq_toFinset_card']