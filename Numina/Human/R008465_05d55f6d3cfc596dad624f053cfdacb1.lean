import Mathlib

-- Define variables and their properties
variable (m n c d : ℝ)
variable (a : ℤ)

/-Given: $m$ and $n$ are opposite numbers, $c$ and $d$ are reciprocals, $a$ is the integer part of $\sqrt{5}$. Find the value of $\sqrt{cd}+2(m+n)-a$.-/
theorem algebra_9388 (h1 : m + n = 0) (h2 : c * d = 1) (h3 : a = ⌊Real.sqrt 5⌋) :
  Real.sqrt (c * d) + 2 * (m + n) - a = -1 := by
  rw [h1, h2]
  rw [Real.sqrt_one, mul_zero, add_zero]
  -- theorem to prove that floor of √5 is 2 
  have sqrt5_floor : ⌊Real.sqrt 5⌋ = 2 := by
    have h1 : Real.sqrt 5 > 2 := by
      apply Real.lt_sqrt_of_sq_lt 
      ring
      linarith
    have h3 : Real.sqrt 5 < 3 := by
      apply (Real.sqrt_lt' ?hy).mpr 
      linarith
      linarith
    apply Int.floor_eq_iff.mpr 
    constructor
    exact le_of_lt h1
    ring
    exact h3
  rw [h3, sqrt5_floor]
  ring