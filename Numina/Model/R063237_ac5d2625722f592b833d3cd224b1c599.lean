import Mathlib

theorem algebra_289076 (x : ℝ) (hx : 4*x^4-12*x^3-7*x^2+22*x+14=0) :
    x=1/2+Real.sqrt 2 ∨ x=1/2-Real.sqrt 2 ∨ x=1+Real.sqrt 3 ∨ x=1-Real.sqrt 3 := by

  have h1 : 4 * x^4 - 12 * x^3 - 7 * x^2 + 22 * x + 14 = 
    4 * (x - (1/2 + Real.sqrt 2)) * (x - (1/2 - Real.sqrt 2)) * (x - (1 + Real.sqrt 3)) * (x - (1 - Real.sqrt 3)) := by

    ring_nf
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ 2 by norm_num)
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ 3 by norm_num)
    -- We need to simplify expressions involving powers of Real.sqrt 2 and Real.sqrt 3.
    simp [h2, h3]
    <;> ring_nf <;> norm_num

  rw [h1] at hx

  cases' (mul_eq_zero.mp hx) with h2 h3

  · cases' (mul_eq_zero.mp h2) with h4 h5

    · cases' (mul_eq_zero.mp h4) with h6 h7

      · -- First factor: x - (1/2 + Real.sqrt 2) = 0
        left
        linarith

      · -- Second factor: x - (1/2 - Real.sqrt 2) = 0
        right
        left
        linarith

    · -- Third factor: x - (1 + Real.sqrt 3) = 0
      right
      right
      left
      linarith

  · -- Fourth factor: x - (1 - Real.sqrt 3) = 0
    right
    right
    right
    linarith