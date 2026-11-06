import Mathlib

/- Show that the function \( f(n) = n^{k} \) is completely multiplicative for every real number \( k \).-/
theorem number_theory_4885 (k a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a ^ k * b ^ k = (a * b) ^ k := by
  -- exact `Real.mul_rpow` in Mathlib
  symm
  apply Real.mul_rpow
  . exact ha.le
  . exact hb.le
