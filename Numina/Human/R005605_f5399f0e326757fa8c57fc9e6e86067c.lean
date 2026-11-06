import  Mathlib

-- If Alex does not sing on Saturday, then she has a $70 \%$ chance of singing on Sunday; however, to rest her voice, she never sings on both days. If Alex has a $50 \%$ chance of singing on Sunday, find the probability that she sings on Saturday.
theorem algebra_609081 (pSat pSun : ℝ) (h1 : pSun = 0.7 * (1 - pSat) + 0 * pSat) (h2 : pSun = 0.5) : pSat = 2 / 7 := by
  -- $\sqrt{\frac{2}{7}}$ Let $p$ be the probability that Alex sings on Saturday. Then, the probability that she sings on Sunday is $.7(1-p)$; setting this equal to .5 gives $p=\frac{2}{7}$.
  simp [h2] at h1
  have : 0.5 / 0.7 = 1 - pSat := by
    rw [h1,mul_div_cancel_left₀] ;norm_num
  have : pSat = 1 - 0.5 / 0.7 := by
    rw [this] ;simp
  rw[this] ;norm_num
   