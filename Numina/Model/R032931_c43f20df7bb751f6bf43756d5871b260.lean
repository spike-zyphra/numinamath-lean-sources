import Mathlib

theorem inequalities_43473 (a b c d e f : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : 0 < d) (h₃ : 0 < e) (h₄ : 0 < f) (h₅ : (a / b : ℝ) < (c / d : ℝ)) (h₆ : (c / d : ℝ) < (e / f : ℝ))
    (h₇ : a * f - b * e = -1) : d ≥ b + f := by
  have h5 : a * d < c * b := by
    have h51 : (a / b : ℝ) < (c / d : ℝ) := h₅
    have pos1 : (b : ℝ) > 0 := by exact_mod_cast h₀
    have pos2 : (d : ℝ) > 0 := by exact_mod_cast h₂
    have h8 : (a : ℝ) * (d : ℝ) < (c : ℝ) * (b : ℝ) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h51
      linarith
    exact_mod_cast h8
  have h6 : c * f < e * d := by
    have h61 : (c / d : ℝ) < (e / f : ℝ) := h₆
    have pos1 : (d : ℝ) > 0 := by exact_mod_cast h₂
    have pos2 : (f : ℝ) > 0 := by exact_mod_cast h₄
    have h8 : (c : ℝ) * (f : ℝ) < (e : ℝ) * (d : ℝ) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mp at h61
      linarith
    exact_mod_cast h8
  by_contra h
  push_neg at h
  have h1 : d ≤ b + f - 1 := by omega
  have h8 : a * (b + f - 1) ≤ c * b - 1 := by
    nlinarith [h5, h1, mul_pos (show 0 < b by linarith) (show 0 < f by linarith)]
  have h9 : c * f ≤ e * (b + f - 1) - 1 := by
    nlinarith [h6, h1, mul_pos (show 0 < b by linarith) (show 0 < f by linarith)]
  -- From h₇: $a * f - b * e = -1$ we get $a * f = b * e - 1$
  have h10 : a * f = b * e - 1 := by linarith
  -- Multiply the various inequalities to get a contradiction.
  nlinarith [mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < d by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < e by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < f by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < d by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < e by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < f by linarith), 
          mul_pos (show 0 < c by linarith) (show 0 < d by linarith), 
          mul_pos (show 0 < c by linarith) (show 0 < e by linarith), 
          mul_pos (show 0 < c by linarith) (show 0 < f by linarith), 
          mul_pos (show 0 < d by linarith) (show 0 < e by linarith), 
          mul_pos (show 0 < d by linarith) (show 0 < f by linarith),
          mul_pos (show 0 < e by linarith) (show 0 < f by linarith)]