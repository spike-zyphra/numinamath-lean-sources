import Mathlib

theorem number_theory_124600 (a b c d e f : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : 0 < d) (h₃ : 0 < e) (h₄ : 0 < f) (h₅ : (a / b : ℝ) < (c / d : ℝ)) (h₆ : (c / d : ℝ) < (e / f : ℝ))
    (h₇ : a * f - b * e = -1) : d ≥ b + f := by 
  have h8 : a * d < b * c := by
    have h9 : (a : ℝ) * (d : ℝ) < (b : ℝ) * (c : ℝ) := by
      have h10 : (a / b : ℝ) < (c / d : ℝ) := h₅
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h10
      linarith
    norm_cast at h9 ⊢
  have h10 : c * f < e * d := by
    have h11 : (c : ℝ) * (f : ℝ) < (e : ℝ) * (d : ℝ) := by
      have h12 : (c / d : ℝ) < (e / f : ℝ) := h₆
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h12
      linarith
    norm_cast at h11 ⊢
  by_contra h
  push_neg at h
  have h11 : d < b + f := by linarith
  nlinarith [mul_pos (show 0 < a by assumption) (show 0 < f by assumption),
          mul_pos (show 0 < b by assumption) (show 0 < d by assumption),
          mul_pos (show 0 < c by assumption) (show 0 < f by assumption),
          mul_pos (show 0 < c by assumption) (show 0 < d by assumption),
          mul_pos (show 0 < a by assumption) (show 0 < d by assumption),
          mul_pos (show 0 < a by assumption) (show 0 < c by assumption),
          mul_pos (show 0 < b by assumption) (show 0 < e by assumption),
          mul_pos (show 0 < a by assumption) (show 0 < f by assumption)]