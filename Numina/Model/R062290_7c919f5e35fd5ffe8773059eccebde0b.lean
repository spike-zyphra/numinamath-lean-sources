import Mathlib

theorem algebra_47373 {a r : ℝ} (hr : r ≠ 0) (ha : a ≠ 0)
    (h5 : a * r^4 = Nat.factorial 7) (h8 : a * r^7 = Nat.factorial 8) :
    a = 315 := by
  have h7 : (Nat.factorial 7 : ℝ) = 5040 := by
    norm_num [Nat.factorial]
  have h8' : (Nat.factorial 8 : ℝ) = 40320 := by
    norm_num [Nat.factorial]
  rw [h7] at h5
  rw [h8'] at h8
  have hr3 : r^3 = 8 := by
    have h1 : a * r^7 = (a * r^4) * r^3 := by ring
    rw [h1] at h8
    nlinarith [h5]
  have hr2 : r = 2 := by
    have h : r^3 - 8 = 0 := by linarith
    have hfactored : (r - 2) * (r^2 + 2*r + 4) = 0 := by
      rw [←h]
      ring
    cases' (mul_eq_zero.mp hfactored) with hr1 h2
    · -- Case r - 2 = 0, so r = 2
      linarith
    · -- Case r^2 + 2r + 4 = 0, show that it's impossible in real numbers
      have : r^2 + 2 * r + 4 > 0 := by 
        nlinarith [sq_nonneg (r + 1), sq_nonneg r]
      linarith -- Contradiction since r^2 + 2r + 4 = 0 < 0
  have ha2 : a = 315 := by
    rw [hr2] at h5 
    nlinarith
  linarith [ha2]