import Mathlib

/- The first term of a geometric sequence is 7, and the 7th term is 5103. What is the 5th term? -/
theorem algebra_21257 {a r : ℝ} (ha : a = 7) (hr : r ≠ 0) (h7 : a * r^6 = 5103) :
    a * r^4 = 567 := by
  -- Substitute a = 7
  subst ha
  -- Simplify h7, and we get r^6 = 729, we write it as (r^2)^3 = 9^3
  replace h7 : (r^2)^3 = 9^3 := by linarith only [h7]
  -- Either r^2 = 9
  -- Or r^2 = -9 and 3 is even
  rw [pow_eq_pow_iff_of_ne_zero (show 3 ≠ 0 by simp)] at h7
  -- But 3 is not even, so r^2 = 9
  simp [show ¬Even 3 by decide] at h7
  -- Simple calculation shows a * r^4 = 567
  calc _ = 7 * (r^2)^2 := by ring
       _ = 7 * 9^2 := by rw [h7]
       _ = 567 := by norm_num
