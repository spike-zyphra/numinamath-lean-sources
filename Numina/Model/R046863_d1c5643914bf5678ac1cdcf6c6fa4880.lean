import Mathlib

theorem inequalities_175857 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a * b + b * c + c * d + d * a = 1) :
    1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) +
    d ^ 3 / (a + b + c) := by 
  have h1 : a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) + d ^ 3 / (a + b + c) ≥ 1 / 3 := by 
    have h2 : a ^ 3 / (b + c + d) ≥ 2 * a^2 / 3 - (b + c + d) * a / 9 := by
      have h1' : 0 < b + c + d := by 
        by_contra h1
        push_neg at h1 
        have h1' : b = 0 := by linarith 
        have h1' : c = 0 := by linarith 
        have h1' : d = 0 := by linarith 
        have h2' : a * b + b * c + c * d + d * a = 0 := by 
          rw [show b = 0 by linarith, show c = 0 by linarith, show d = 0 by linarith]
          all_goals nlinarith 
        nlinarith 
      apply (le_div_iff₀ (by positivity)).mpr 
      nlinarith [sq_nonneg (a - (b + c + d) / 3), 
          sq_nonneg (a * 3 - (b + c + d)), 
          mul_nonneg ha (show 0 ≤ b + c + d by positivity)
        ]
    have h3 : b ^ 3 / (c + d + a) ≥ 2 * b^2 / 3 - (c + d + a) * b / 9 := by 
      have h2' : 0 < c + d + a := by 
        by_contra h2 
        push_neg at h2 
        have h2' : c = 0 := by linarith 
        have h2' : d = 0 := by linarith 
        have h2' : a = 0 := by linarith 
        have h2' : a * b + b * c + c * d + d * a = 0 := by 
          rw [show a = 0 by linarith, show c = 0 by linarith, show d = 0 by linarith]
          all_goals nlinarith 
        nlinarith 
      apply (le_div_iff₀ (by positivity)).mpr 
      nlinarith [sq_nonneg (b - (c + d + a) / 3), 
          sq_nonneg (b * 3 - (c + d + a)), 
          mul_nonneg hb (show 0 ≤ c + d + a by positivity)
        ]
    have h4 : c ^ 3 / (d + a + b) ≥ 2 * c^2 / 3 - (d + a + b) * c / 9 := by 
      have h3' : 0 < d + a + b := by 
        by_contra h3 
        push_neg at h3 
        have h3' : d = 0 := by linarith 
        have h3' : a = 0 := by linarith 
        have h3' : b = 0 := by linarith 
        have h3' : a * b + b * c + c * d + d * a = 0 := by 
          rw [show a = 0 by linarith, show b = 0 by linarith, show d = 0 by linarith]
          all_goals nlinarith 
        nlinarith 
      apply (le_div_iff₀ (by positivity)).mpr 
      nlinarith [sq_nonneg (c - (d + a + b) / 3), 
          sq_nonneg (c * 3 - (d + a + b)), 
          mul_nonneg hc (show 0 ≤ d + a + b by positivity)
        ]
    have h5 : d ^ 3 / (a + b + c) ≥ 2 * d^2 / 3 - (a + b + c) * d / 9 := by 
      have h4' : 0 < a + b + c := by 
        by_contra h4 
        push_neg at h4 
        have h4' : a = 0 := by linarith 
        have h4' : b = 0 := by linarith 
        have h4' : c = 0 := by linarith 
        have h4' : a * b + b * c + c * d + d * a = 0 := by 
          rw [show a = 0 by linarith, show b = 0 by linarith, show c = 0 by linarith]
          all_goals nlinarith 
        nlinarith 
      apply (le_div_iff₀ (by positivity)).mpr 
      nlinarith [sq_nonneg (d - (a + b + c) / 3), 
          sq_nonneg (d * 3 - (a + b + c)), 
          mul_nonneg hd (show 0 ≤ a + b + c by positivity)
        ]
    have h6 : a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) +
        d ^ 3 / (a + b + c) ≥ 2 * a^2 / 3 - (b + c + d) * a / 9 + (2 * b^2 / 3 - (c + d + a) * b / 9) + (2 * c^2 / 3 - (d + a + b) * c / 9) + (2 * d^2 / 3 - (a + b + c) * d / 9) := by
      linarith [h2, h3, h4, h5]
    have h7 : 2 * a^2 / 3 - (b + c + d) * a / 9 + (2 * b^2 / 3 - (c + d + a) * b / 9) + (2 * c^2 / 3 - (d + a + b) * c / 9) + (2 * d^2 / 3 - (a + b + c) * d / 9) ≥ 1 / 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), h, 
        mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg ha hd, 
        mul_nonneg hb hc, mul_nonneg hb hd, 
        mul_nonneg hc hd]
    linarith [h6, h7]
  linarith [h1]