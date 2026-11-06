import Mathlib

theorem algebra_172960 (d : ℝ) (h₀ : d > 0) (h₁ : 1.2 * (d / 6) = (d - 5) / (1.6 * (d / 6))) :
    d = 45 := by

  have h₂ : d ≠ 0 := by linarith
  have h₃ : 1.6 * (d / 6) ≠ 0 := by
    by_contra h
    have : d = 0 := by
      norm_num at h
      linarith
    contradiction

  -- rewrite the equation with cross multiply to clear denominators
  have h₄ : 1.2 * (d / 6) * (1.6 * (d / 6)) = d - 5 := by
    have h₃' : 1.6 * (d / 6) ≠ 0 := h₃
    field_simp [h₃'] at h₁ ⊢
    linarith

  -- rearranged to clear fractions: 1.92 * (d ^ 2) / 36 = d - 5
  have eq3 : 1.92 * d ^ 2 = 36 * (d - 5) := by
    ring_nf at h₄ ⊢
    linarith [h₄]

  -- Rearranged: 1.92 * d^2 - 36 * d + 180 = 0
  have h₆ : 1.92 * d ^ 2 - 36 * d + 180 = 0 := by 
    linarith [eq3]

  -- Multiply through by 100 to clear decimals: 192 * d^2 - 3600 * d + 18000 = 0
  have h₇ : 192 * d ^ 2 - 3600 * d + 18000 = 0 := by 
    ring_nf at h₆ ⊢
    linarith [h₆]

  -- Simplify by GCD (which is 24): 8 * d^2 - 150 * d + 750 = 0
  have h₈ : 8 * d ^ 2 - 150 * d + 750 = 0 := by 
    nlinarith [h₇]

  -- Now show contradiction from `h₈` and `h₀`. Since discriminant of `h₈` is negative. So inconsistency implies goal d=45.
  nlinarith [sq_nonneg (d - 45), sq_nonneg (d * 8 - 150 * 4), sq_nonneg (d - 5), sq_nonneg (4 * d - 75), sq_nonneg (d * (d - 45 / 4)), sq_nonneg ((d - 5) * 8), sq_nonneg ((8 * d ^ 2 - 150 * d + 750) * 4), sq_nonneg ((d) ^ 2), sq_pos_of_pos h₀]