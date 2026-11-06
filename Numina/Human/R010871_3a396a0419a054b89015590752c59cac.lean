import Mathlib

/- If $a,b,c,d$ are positive real numbers such that $a,b,c,d$ form an increasing arithmetic sequence and $a,b,d$ form a geometric sequence, then find the value of $\dfrac{a}{d}.$ -/
theorem algebra_20361 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hseq : ∃ d, b = a + d ∧ c = b + d ∧ d = c + d)
    (hge : ∃ r, b = a * r ∧ d = b * r) :
    a / d = 1 / 4 := by
  cases' hseq with d h
  cases' hge with r h
  nlinarith