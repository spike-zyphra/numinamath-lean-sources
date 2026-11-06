import Mathlib

theorem algebra_302977 {a : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = (x + a) * (abs (x - a + 1) + abs (x - 3)) - 2 * x + 4 * a)
    (h₁ : ∀ x, ∃ y, f x = -y ∧ f (-x) = y) :
    a = -2 / 3 := by

  have h2' : f 0 = 0 := by
    have h20 := h₁ 0
    rcases h20 with ⟨y0, h21, h22⟩
    have h20' : f (- (0 : ℝ)) = y0 := h22
    simp at h20' 
    linarith

  have eq1 : f 0 = (0 + a) * (abs (0 - a + 1) + abs (0 - 3)) - 2 * 0 + 4 * a := h₀ 0
  rw [eq1] at h2'

  have h3 : abs (0 - 3 : ℝ) = 3 := by
    norm_num [abs_of_nonneg]

  have h8 : abs (0 - a + 1 : ℝ) = abs (1 - a : ℝ) := by 
    ring_nf

  rw [h3, h8] at h2'

  by_cases h9 : (1 - a : ℝ) ≥ 0
  · -- Case where 1 - a ≥ 0, so |1 - a| = 1 - a
    have ha2 : abs (1 - a : ℝ) = 1 - a := by
      rw [abs_of_nonneg h9]
    rw [ha2] at h2'
    have h10 : a * (8 - a) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h10) with h11 h12
    · -- Case h11: a = 0
      have ha0 : a = 0 := by
        linarith
      have h3 := h₁ 3
      rcases h3 with ⟨y3, h31, h32⟩
      have eq3 : f 3 = (3 + a) * (abs (3 - a + 1) + abs (3 - 3)) - 2 * 3 + 4 * a := h₀ 3
      have eq3' : f (-3) = (-3 + a) * (abs (-3 - a + 1) + abs (-3 - 3)) - 2 * (-3) + 4 * a := h₀ (-3)
      rw [eq3] at h31
      rw [eq3'] at h32
      rw [show a = 0 by linarith [ha0]] at h31 h32
      norm_num [abs_of_nonneg, abs_of_neg] at h31 h32
      all_goals linarith
    · -- Case h12: 8 - a = 0, so a = 8
      have ha8 : a = 8 := by
        linarith
      have h4 := h₁ 0
      linarith [show a ≤ 1 by linarith [h9, ha8]]
  · -- Case where 1 - a < 0, so |1 - a| = a - 1
    have ha2 : abs (1 - a : ℝ) = a - 1 := by
      rw [abs_of_neg (lt_of_not_ge h9)]
      ring
    rw [ha2] at h2'
    nlinarith [h₁ 1, h₁ 2, h₁ 4, h₁ 5]