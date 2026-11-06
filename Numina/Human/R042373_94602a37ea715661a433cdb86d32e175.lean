import Mathlib

/-Simplify the numerical expression $\frac{6-\log _{14} 2401}{4-\log _{14} 49}$ and write it in the form of a logarithm $\log _{28} n$, where $n$ is a natural number.-/
theorem algebra_206019 : (6 - Real.logb 14 2401) / (4 - Real.logb 14 49) = Real.logb 28 56 := by
  -- $$ \begin{aligned} \frac{6-\log _{14} 2401}{4-\log _{14} 49} & =\frac{6-4 \log _{14} 7}{4-2 \log _{14} 7}=\frac{3-2 \log _{14} 7}{2-\log _{14} 7} & & 1 \text { bod } \ & =\frac{\log _{14} 14^{3}-\log _{14} 7^{2}}{\log _{14} 14^{2}-\log _{14} 7} & & 1 \text { bod } \ & =\frac{\log _{14} \frac{14^{3}}{7^{2}}}{\log _{14} \frac{14^{2}}{7}} & & 1 \text { bod } \ & =\frac{\log _{14} 56}{\log _{14} 28} & & 1 \text { bod } \ & =\log _{28} 56 & & 1 \text { bod } \end{aligned} $$
  -- $\log _{14} 2401=4 \log _{14} 7$
  have h1 : Real.logb 14 2401 = 4 * Real.logb 14 7 := by
    rw [show (2401 : ℝ) = 7 ^ 4 by norm_num]
    simp [Real.logb_pow]
  -- $\log _{14} 49=2 \log _{14} 7$
  have h2 : Real.logb 14 49 = 2 * Real.logb 14 7 := by
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num]
    simp [Real.logb_pow]
  rw [h1, h2]
  have h3 : (6 - 4 * Real.logb 14 7) / (4 - 2 * Real.logb 14 7) = Real.logb 28 56 := by
    -- $\frac{\log _{14} 56}{\log _{14} 28}  =\log _{28} 56$
    have h4 : Real.logb 28 56 = Real.logb 14 56 / Real.logb 14 28 := by
      field_simp [Real.logb]
    rw [h4]
    have h5 : Real.logb 14 56 = Real.logb 14 7 + 3 * Real.logb 14 2 := by
      have h56 : (56 : ℝ) = 7 * (2 ^ 3) := by norm_num
      rw [h56]
      simp [Real.logb_mul, Real.logb_pow]
    have h6 : Real.logb 14 28 = Real.logb 14 7 + 2 * Real.logb 14 2 := by
      have h28 : (28 : ℝ) = 7 * (2 ^ 2) := by norm_num
      rw [h28]
      simp [Real.logb_mul, Real.logb_pow]
    rw [h5, h6]
    have h7 : Real.logb 14 2 > 0 := by
      apply Real.logb_pos
      all_goals norm_num
    have h8 : Real.logb 14 7 > 0 := by
      apply Real.logb_pos
      all_goals norm_num
    have h9 : Real.logb 14 14 = 1 := Real.logb_self_eq_one (by norm_num)
    have h10 : Real.logb 14 7 + Real.logb 14 2 = 1 := by
      have h14 : Real.logb 14 14 = 1 := Real.logb_self_eq_one (by norm_num)
      have h14_2 : Real.logb 14 14 = Real.logb 14 (7 * 2) := by norm_num
      rw [h14_2] at h14
      simp [Real.logb_mul] at h14
      linarith
    have h11 : Real.logb 14 7 + 2 * Real.logb 14 2 ≠ 0 := by
      nlinarith [h7, h8]
    have h12 : 4 - 2 * Real.logb 14 7 ≠ 0 := by
      by_contra h
      have h13 : Real.logb 14 7 = 2 := by linarith
      have h14 : (14 : ℝ) ^ (2 : ℝ) = 7 := by
        rw [←h13]
        field_simp [Real.rpow_logb]
      norm_num at h14
    field_simp [h11, h12]
    nlinarith [h10, sq_nonneg (Real.logb 14 7), sq_nonneg (Real.logb 14 2), h7, h8]
  linarith