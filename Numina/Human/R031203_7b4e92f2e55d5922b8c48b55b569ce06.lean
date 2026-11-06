import Mathlib


/-What is the sum of all values of $x$ for which $\sqrt{(x+3)^{2}} = 7$?-/
theorem algebra_5682 {r : Set ℝ} (hr : r = {x | √((x + 3)^2) = 7 }) :
    r = {4, -10} ∧ (∑x∈{4, -10}, x = -6) := by
  constructor
  . -- r = {4, -10}
    ext x
    rw [hr]
    constructor
    . -- x ∈ {x | √((x + 3) ^ 2) = 7} → x ∈ {4, -10}
      intro hx
      simp at hx
      rw [Real.sqrt_sq_eq_abs, abs] at hx
      simp
      by_cases h: x + 3 > 0
      . -- x + 3 = 7
        have : x + 3 > -(x + 3) := by linarith
        have : (x + 3)⊔-(x + 3) = x + 3 := by
          apply max_eq_left
          linarith
        rw [this] at hx
        have : x = 4 := by linarith
        exact Or.inl this
      . -- x + 3 = -7
        simp at h
        have : -(x + 3) ≥ x + 3 := by linarith
        have : (x + 3)⊔-(x + 3) = -(x + 3) := by
          apply max_eq_right
          linarith
        rw [this] at hx
        have : x = -10 := by linarith
        exact Or.inr this
    . -- x ∈ {4, -10} → x ∈ {x | √((x + 3) ^ 2) = 7}
      simp
      intro hx
      rw [Real.sqrt_sq_eq_abs, abs]
      rcases hx
      . have : x + 3 > -(x + 3) := by linarith
        have : (x + 3)⊔-(x + 3) = x + 3 := by
          apply max_eq_left
          linarith
        repeat linarith
      . have : -(x + 3) ≥ x + 3 := by linarith
        have : (x + 3)⊔-(x + 3) = -(x + 3) := by
          apply max_eq_right
          linarith
        repeat linarith
  . -- ∑x∈{4, -10}, x = -6
    rw [Finset.sum_insert]
    repeat simp


