import Mathlib

theorem algebra_267260 {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 24) (hsum : x + y = 11) :
    max x y - min x y = 5 := by
  have h1 : x ≤ 11 := by
    have h2 : y = 11 - x := by linarith
    rw [h2] at hxy
    have h3 : x * (11 - x) = 24 := hxy
    have h4 : x * (11 - x) - 24 = 0 := by linarith
    have h5 : x^2 - 11 * x + 24 = 0 := by
      ring_nf at h4 ⊢
      linarith
    have h6 : x^2 - 11 * x + 24 = (x - 8) * (x - 3) := by
      ring
    rw [h6] at h5
    cases' (mul_eq_zero.1 h5) with h7 h8
    · -- Case x - 8 = 0, so x = 8
      have hx8 : x = 8 := by linarith
      linarith
    · -- Case x - 3 = 0, so x = 3
      have hx3 : x = 3 := by linarith
      linarith
  have h2 : y = 11 - x := by linarith
  rw [h2] at hxy
  have h3 : x * (11 - x) = 24 := hxy
  have h4 : x * (11 - x) - 24 = 0 := by linarith
  have h5 : x^2 - 11 * x + 24 = 0 := by
    ring_nf at h4 ⊢
    linarith
  have h6 : x^2 - 11 * x + 24 = (x - 8) * (x - 3) := by
    ring
  rw [h6] at h5
  cases' (mul_eq_zero.1 h5) with h7 h8
  · -- Case x - 8 = 0, so x = 8
    have hx8 : x = 8 := by linarith
    have hy3 : y = 3 := by
      have h : x + y = 11 := hsum
      rw [hx8] at h
      linarith
    rw [hx8, hy3]
    all_goals norm_num [max_eq_left_of_lt, min_eq_right_of_lt]
  · -- Case x - 3 = 0, so x = 3
    have hx3 : x = 3 := by linarith
    have hy8 : y = 8 := by
      have h : x + y = 11 := hsum
      rw [hx3] at h
      linarith
    rw [hx3, hy8]
    all_goals norm_num [max_eq_right_of_lt, min_eq_left_of_lt]