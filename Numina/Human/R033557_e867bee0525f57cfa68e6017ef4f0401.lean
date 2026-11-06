import Mathlib
open Real

/- If x = t^(1/(t-1)) and y = t^(t/(t-1)), t > 0, t ≠ 1, a relation between x and y is:
(A) y^x = x^(1 / y) （ (B) y^(1 / x) = x^y （ (C) y^x = x^y (D) x^x = y^y (E) none of these -/
theorem algebra_96016 {x y t : ℝ} (ht : t > 0) (ht1 : t ≠ 1)
(hx : x = t ^ ((1 : ℝ) / (t - 1))) (hy : y = t ^ (t / (t - 1))) :
y ^ x = x ^ y := by
  -- preparing some inequalities
  have ht0  : t≥0   := le_of_lt ht
  have ht1' : t-1≠0 := by intro hh;apply ht1;linarith
  -- substituting and expanding
  rw [hx,hy,← Real.rpow_mul ht0,← Real.rpow_mul ht0]
  -- rearranging the term in LHS to match RHS
  calc t^(t/(t-1)                   * t^(1/(t-1)))
     = t^(1/(t-1) * t^((t-1)/(t-1)) * t^(1/(t-1)))  := by field_simp [ht1']
   _ = t^(1/(t-1) * t^((t-1)/(t-1)  +    1/(t-1)))  := by rw[mul_assoc, ← Real.rpow_add ((by simp[ht]):0<t)]
   _ = t^(1/(t-1) * t^(                  t/(t-1)))  := by field_simp [ht1']