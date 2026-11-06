import Mathlib

/- Let P0(x)=x^3+313x^2-77x-8. For integers n>=1, define Pn(x)=Pn-1(x-n). What is the coefficient of x in P20(x) -/
open Polynomial
theorem algebra_96164
  {P : ℤ  → Polynomial ℤ}
  (hP0 : P 0 = X ^ 3 + 313 * X ^ 2 - 77 * X - 8)
  (hP : ∀ n ≥ 1, (P n) = (P (n - 1)).comp (X - (↑n:Polynomial ℤ))) :
  (P 20).coeff 1 = 763
:= by
  -- use the recursive definition of P to expand P 20
  simp [hP,hP0]
  -- expand the polynomial
  ring
  simp
  -- obtain the coefficients
  rw [← Int.cast_one,← C_eq_intCast,coeff_C]
  rw [← @Int.cast_ofNat _ _ 44100,← C_eq_intCast,coeff_C]
  rw [← @Int.cast_ofNat _ _ 9261000,← C_eq_intCast,coeff_C]
  norm_num