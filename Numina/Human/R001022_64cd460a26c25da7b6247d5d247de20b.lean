import Mathlib

/- What is the volume, in cubic centimeters, of a right rectangular prism with all integer edge lengths, and faces having areas of $30, 180$ and $24$ square centimeters? -/
theorem algebra_19934 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a * b = 30) (h2 : a * c = 180) (h3 : b * c = 24) :
    a * b * c = 360 := by
  suffices h : (a * b * c) ^ 2 = 360 ^ 2 by
    rw [sq_eq_sq] at h
    exact h
    positivity
    norm_num
  -- Use the fact that (a * b * c) ^ 2 = (a * b) * (a * c) * (b * c).
  rw [show (a * b * c) ^ 2 = (a * b) * (a * c) * (b * c) by ring_nf]
  rw [h1, h2, h3]
  norm_num
