import Mathlib

theorem algebra_11411 {p : ℝ → ℝ → ℝ}
    (hp : ∀ x y, (x ≥ 0 ∧ y ≥ 0 → p x y = x + y) ∧
      (x < 0 ∧ y < 0 → p x y = x - 2 * y) ∧
      (x ≥ 0 ∧ y < 0 ∨ x < 0 ∧ y ≥ 0 → p x y = 3 * x + y)) :
    p (p 1 (-1)) (p (-5) (-2)) = 5 := by
  have h1 : p 1 (-1) = 2 := by
    have h := (hp 1 (-1)).2.2
    norm_num at h
    linarith
  have h2 : p (-5) (-2) = -1 := by
    have h := (hp (-5) (-2)).2.1
    norm_num at h
    linarith
  have h3 : p 2 (-1) = 5 := by
    have h := (hp 2 (-1)).2.2
    norm_num at h
    linarith
  rw [h1, h2]
  exact h3