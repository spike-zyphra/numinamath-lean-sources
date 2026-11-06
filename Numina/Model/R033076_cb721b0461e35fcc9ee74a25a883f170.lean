import Mathlib

theorem algebra_112050 (t w g r: ℕ) (h0 : w>0∧ r>0) (hg : g > 1000)
    (ht : w + g + r = t)
    (h1: ((w/ (w + g)):ℝ)+ (((g+r)/t):ℝ) = 1.46)
    :
    w > 850 := by 
  have h2 : (w:ℝ) > (0 : ℝ):= by exact_mod_cast h0.1
  have h3 : (r:ℝ) > (0 : ℝ):= by exact_mod_cast h0.2
  have h4 : (g:ℝ) > (1000 : ℝ):= by exact_mod_cast hg
  have h5 : (w + g + r : ℝ) = (t : ℝ) := by
    exact_mod_cast ht
  by_contra h
  push_neg at h
  have h13 : w ≤ 850 := by
    omega
  have h14 : (w : ℝ) ≤ (850 : ℝ) := by
    exact_mod_cast h13
  have eq4 : (w : ℝ) / ((w + g) : ℝ) + ((g + r : ℝ) / ((w + g + r) : ℝ)) = 1.46 := by 
    have eq5 : (t : ℝ) = (w + g + r : ℝ) := by 
      nlinarith
    have eq6 : ((g + r : ℝ) / (t : ℝ)) = ((g + r : ℝ) / (w + g + r : ℝ)) := by 
      rw [eq5]
    have eq7 : ((w / (w + g) : ℝ) + ((g + r) / t) ) = 1.46 := by 
      linarith
    rw [eq6] at eq7
    linarith
  have h9 : (w : ℝ) * (w + g + r : ℝ) + (g + r : ℝ) * (w + g : ℝ) = 1.46 * ((w + g : ℝ) * (w + g + r : ℝ)) := by
    field_simp [(show ((w + g) : ℝ) ≠ 0 by
      positivity ), 
      (show ((w + g + r) : ℝ) ≠ 0 by 
        positivity ) ] at eq4 ⊢
    nlinarith
  have h15 : (w : ℝ) * (w + g + r : ℝ) + (g + r : ℝ) * (w + g : ℝ) > 1.46 * ((w + g : ℝ) * (w + g + r : ℝ)) := by 
    nlinarith [sq_nonneg ( (w : ℝ) - 850 ), sq_nonneg ( (g : ℝ) - 1000 ), sq_nonneg ( (r : ℝ) - 850 ), 
      mul_pos h2 (show (0 : ℝ) < (g : ℝ) by nlinarith), 
        h2, h3, h4, 
        mul_pos h2 (show (0 : ℝ) < (r : ℝ) by linarith)
        ]
  nlinarith [show (w * (w + g + r) + (g + r) * (w + g) : ℝ) > 0 by positivity, show ( (w + g) * (w + g + r) : ℝ ) > 0 by positivity, h2, h3, h4]