import Mathlib

open Polynomial

/- Among all polynomials $P(x)$ with integer coefficients for which $P(-10)=145$ and $P(9)=164$, compute the smallest possible value of $|P(0)|$. -/
theorem algebra_610261 :
    IsLeast {abs (eval 0 P) | (P : ℤ[X]) (_ : P.eval (-10) = 145) (_ : P.eval 9 = 164)} 25 := by
  constructor
  -- We first show that 25 is a possible value
  -- Which is witnessed by the polynomial 2 * X ^ 2 + 3 * X - 25
  . use 2 * X ^ 2 + 3 * X - 25
    simp
  -- We now show that any polynomial P with the given properties satisfies |P(0)| ≥ 25
  . rintro z ⟨P, h₁, h₂, rfl⟩
    -- We have a - b ∣ P(a) - P(b) for any a, b ∈ ℤ
    -- So 10 ∣ P(0) - 145 and 9 ∣ 164 - P(0)
    replace h₁ : 10 ∣ P.eval 0 - 145 := by
      convert Polynomial.sub_dvd_eval_sub 0 (-10) P
      exact h₁.symm
    replace h₂ : 9 ∣ 164 - P.eval 0 := by
      convert Polynomial.sub_dvd_eval_sub 9 0 P
      exact h₂.symm
    -- And now omega can solve the rest
    rw [le_abs]
    omega
