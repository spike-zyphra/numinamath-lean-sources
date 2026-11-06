import Mathlib

theorem algebra_245759 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : abs (a * b - 2) = -(abs (b - 1))) :
    ∑ i ∈ Finset.range 2021, (1 / ((a + i) * (b + i))) = 2021 / 2022 := by
  have h1 : abs (a * b - 2) ≥ 0 := by positivity
  have h2 : abs (b - 1) ≥ 0 := by positivity
  have h3 : abs (a * b - 2) = 0 := by 
    linarith [h, h1, h2]
  have h4 : abs (b - 1) = 0 := by 
    linarith [h, h1, h2]
  have h5 : a * b - 2 = 0 := by 
    rwa [abs_eq_zero] at h3
  have h6 : b - 1 = 0 := by 
    rwa [abs_eq_zero] at h4
  have hb' : b = 1 := by linarith
  have ha' : a = 2 := by 
    rw [hb'] at h5
    nlinarith
  rw [ha', hb']
  -- Compute the sum
  norm_num [Finset.sum_range_succ]