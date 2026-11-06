import Mathlib
open Real

/- When c is added to both the numerator and denominator of the fraction a/b, a≠b, b≠0, the value of the fraction is changed to c/d. Then x equals:
(A) 1/(c-d) (B) (ad-bc)/(c-d) (C) (ad-bc)/(c+d) (D) (bc-ad)/(c-d) (E) (bc+ad)/(c-d) -/
theorem algebra_95812 {a b c d x : ℝ} (ha : a ≠ b) (hb : b ≠ 0) (hd : d ≠ 0) (hbx: b + x ≠ 0) (hcd: c - d ≠ 0)
(h : (a + x) / (b + x) = c / d) :
x = (a * d - b * c) / (c - d) := by
  -- solve by rearranging
  rw [← mul_left_inj' hd,div_mul c d d] at h; simp [hd] at h
  rw [mul_comm,mul_div] at h
  rw [← mul_left_inj' hbx,div_mul] at h; simp [hbx] at h
  rw [← mul_left_inj' hcd,div_mul]; simp [hcd]
  linarith