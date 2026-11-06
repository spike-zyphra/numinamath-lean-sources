import Mathlib

theorem algebra_2662 {x : ℝ} (hx : 0 < x) (h : (1 + x / 100) ^ 2 = 1.44) : x = 20 := by
  have h1 : (1 + x / 100 : ℝ) ^ 2 - (1.44 : ℝ) = 0 := by
    linarith
  have h2 : ((1 + x / 100 : ℝ) - 1.2) * ((1 + x / 100 : ℝ) + 1.2) = 0 := by
    ring_nf at h1 ⊢
    norm_num at h1 ⊢
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- First case: (1 + x / 100) - 1.2 = 0, which means 1 + x/100 = 1.2
    have h5 : (x : ℝ) = 20 := by 
      norm_num at h3 
      linarith 
    exact h5
  · -- Second case: (1 + x / 100) + 1.2 = 0, which means 1 + x/100 = -1.2
    have h5 : (x : ℝ) < (0 : ℝ) := by 
      norm_num at h4 
      nlinarith
    linarith -- contradicts hx: 0 < x