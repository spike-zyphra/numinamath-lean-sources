import Mathlib

theorem algebra_301253 {f : ℝ → ℝ} (h : ∀ x, 2 * f (1 - x) + 1 = x * f x) :
    ∀ x, f x = (x - 3) / (x ^ 2 - x + 4) := by
  intro x
  have eq1 := h x
  have eq3 : 2 * f x + 1 = (1 - x) * f (1 - x) := by
    have h2 := h (1 - x)
    have eq4 : 1 - (1 - x : ℝ) = x := by
      ring
    rw [eq4] at h2
    linarith
  by_cases hne : 1 - x = 0
  · -- Case where 1 - x = 0, so x = 1
    have hx1 : x = 1 := by linarith
    rw [hx1]
    have eq5 : f 1 = -1 / 2 := by
      -- Use h 1 and h 0
      have h1 := h 1
      have h2 := h (1 - 1)
      -- Simplify them
      norm_num at h1 h2
      -- Combine with h 0
      linarith [h 0, h1, h2]
    rw [eq5]
    all_goals norm_num
    <;> nlinarith
  · -- Case where 1 - x ≠ 0
    have eq4 : f (1 - x) = (2 * f x + 1) / (1 - x) := by
      have hne' : 1 - x ≠ 0 := hne
      field_simp [(show (1 - x : ℝ) ≠ 0 by assumption)]
      linarith [eq3]
    rw [eq4] at eq1
    have hne' : 1 - x ≠ 0 := hne
    have eq5 : f x * (x ^ 2 - x + 4) = x - 3 := by
      field_simp [hne'] at eq1 ⊢
      nlinarith [sq_nonneg (f x), sq_nonneg (x ^ 2 - x + 4), sq_pos_of_ne_zero (show (1 - x : ℝ) ≠ 0 by assumption), sq_nonneg (x - 1 / 2)]
    have hx2 : x ^ 2 - x + 4 ≠ 0 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    field_simp [hx2]
    <;> nlinarith