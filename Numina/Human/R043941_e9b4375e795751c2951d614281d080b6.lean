import Mathlib
open Polynomial

/- 7. B1 (CAN 2) Let $p(x)$ be a cubic polynomial with integer coefficients with leading coefficient 1 
   and with one of its roots equal to the product of the other two. 
   Show that $2 p(-1)$ is a multiple of $p(1)+p(-1)-2(1+p(0))$. -/
theorem algebra_23847 {p : Polynomial ℤ} (hp : p.degree = 3)
    (hmonic : p.coeff 3 = 1) (r s : ℤ)
    (hroots : p = (X - C r) * (X - C s) * (X - C (r * s))) :
    p.eval 1 + p.eval (-1) - 2 * (1 + p.eval 0) ∣ 2 * p.eval (-1) := by

  -- Evaluate p(-1) using the root factorization
  have h₁ : p.eval (-1) =
    (-1 - r) * (-1 - s) * (-1 - r * s) := by
    rw [hroots]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
  
  -- Evaluate p(1) using the root factorization
  have h₂ : p.eval 1 =
      (1 - r) * (1 - s) * (1 - r * s) := by
      rw [hroots]
      simp only [eval_mul, eval_sub, eval_X, eval_C]

  -- Evaluate p(0) using the root factorization
  have h₃ : p.eval 0 =
    (-r) * (-s) * (-r * s) := by
    rw [hroots]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    ring_nf

  -- Define auxiliary expressions A = (1 + r)(1 + s)(1 + rs), B = (1 + r)(1 + s)
  let A := (1 + r) * (1 + s) * (1 + r * s)
  let B := (1 + r) * (1 + s)

  -- Simplify 2 * p(-1) as -2 * A
  have tmp: 2 * p.eval (-1) = -2 * A := by
    rw [h₁]
    ring_nf

  -- Simplify p(1) + p(-1) - 2 * (1 + p(0)) as -2 * B
  have tmp1: p.eval 1 + p.eval (-1) - 2 * (1 + p.eval 0) = -2 * B := by
    rw [h₁, h₂, h₃]
    ring_nf
  
  -- Conclude the divisibility by showing 2 * p(-1) = (1 + r * s) * (p(1) + p(-1) - 2 * (1 + p(0)))
  use (1 + r * s)
  rw[tmp, tmp1]
  simp[A,B]
  ring