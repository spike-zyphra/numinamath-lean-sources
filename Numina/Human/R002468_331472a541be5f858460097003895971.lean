import Mathlib
open Real
/- In the expansion of (a-1/(√a))^7 the coefficient of a^(-1/2) is
   (A) -7 (B) 7 (C) -21 (D) 21 (E) 35
-/
theorem algebra_93886 (n:ℕ) (h:(7-n:ℚ)-(1/2)*n=-1/2)
: (Nat.choose 7 n) * (-1 : ℝ)^5 = -21 := by
  -- By the Binomial Theorem, the coefficients of each term of the expansion are
  -- Nat.choose 7 n
  -- where, in our case we have (7-n)-(1/2)*n=-1/2
  -- solving this equation gives us n=5
  field_simp at h
  have hn: (n:ℚ)=5:=by linarith
  norm_cast at hn;rw [hn]
  -- substituting n=5 to the binomial expression and we can calculate the final result
  rw [
    (by reduce;rfl:Nat.choose 7 5 = 21),
    (by linarith:(-1:ℝ) ^ 5=-1)
  ]
  norm_cast