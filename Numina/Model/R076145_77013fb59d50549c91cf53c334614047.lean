import Mathlib

theorem algebra_297051 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : abs (a * b + 2) + abs (a + 1) = 0) :
    ∑ i ∈ Finset.range 2006, (1 / ((a - (i + 1)) * (b + (i + 1)))) = -1003 / 2008 := by
  have h1 : abs (a * b + 2) = 0 := by
    linarith [abs_nonneg (a * b + 2), abs_nonneg (a + 1)]
  have h2 : abs (a + 1) = 0 := by
    linarith [abs_nonneg (a * b + 2), abs_nonneg (a + 1)]
  have h3 : a * b + 2 = 0 := by 
    rwa [abs_eq_zero] at h1
  have h4 : a + 1 = 0 := by 
    rwa [abs_eq_zero] at h2
  have ha_val : a = -1 := by linarith
  have hb_val : b = 2 := by
    rw [ha_val] at h3
    linarith
  rw [ha_val, hb_val]
  norm_num
  <;> try { native_decide }
  <;> try { linarith }