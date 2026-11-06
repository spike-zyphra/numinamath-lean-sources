import Mathlib

theorem inequalities_220540
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (h : a + b + c + d = 1) :
    a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) + d / (d ^ 2 + 1) ≤
    16 / 17 := by

  have h2 : ∀ x : ℝ, 0 < x → x / (x ^ 2 + 1) ≤ (240 / 289) * x + 8 / 289 := by
    intro x hx
    have h3 : x ^ 2 + 1 > 0 := by
      nlinarith [sq_nonneg x]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (x ^ 2 - 1 / 4), sq_nonneg (x - 1 / 4), sq_nonneg (x * (x - 1 / 4)), sq_nonneg ((x - 1 / 4) * (x - 1 / 4)), sq_nonneg (x - 1 / 2), sq_nonneg (x * (x - 1 / 2)), sq_nonneg ((x - 1) * (x - 1)), sq_nonneg ((x - 1 / 4) * (x - 1)), mul_pos hx (show 0 < x by linarith), sq_nonneg (x ^ 2 - 1)]

  have h2a : a / (a ^ 2 + 1) ≤ (240 / 289) * a + 8 / 289 := h2 a ha
  have h2b : b / (b ^ 2 + 1) ≤ (240 / 289) * b + 8 / 289 := h2 b hb
  have h2c : c / (c ^ 2 + 1) ≤ (240 / 289) * c + 8 / 289 := h2 c hc
  have h2d : d / (d ^ 2 + 1) ≤ (240 / 289) * d + 8 / 289 := h2 d hd

  have h3 : a / (a ^ 2 + 1) + b / (b ^ 2 + 1) + c / (c ^ 2 + 1) + d / (d ^ 2 + 1) ≤ (240 / 289) * (a + b + c + d) + 32 / 289 := by
    linarith [h2a, h2b, h2c, h2d]

  rw [show a + b + c + d = 1 by linarith] at h3
  norm_num at h3 ⊢
  all_goals linarith