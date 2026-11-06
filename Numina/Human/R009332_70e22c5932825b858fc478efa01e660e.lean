import Mathlib

/- Suppose a is 150% of b. What percent of a is 3b?
(A) 50 (B) 66+ 2/3 (C) 150 (D) 200(E) 450 -/
theorem algebra_92954 {a b : ℝ} (ha : a = 150 / 100 * b) (hb : b ≠ 0) :
(3 * b) / a = 200 / 100 := by
    --substitute ha in the claim and solve with linear arithmetic
    rw[ha]
    field_simp
    ring_nf