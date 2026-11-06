import Mathlib

/- What is $2^{-1} + 2^{-2} + 2^{-3} + 2^{-4} + 2^{-5} + 2^{-6} \pmod{13}$? -/
theorem number_theory_11014 : (2 ^ 1 : ZMod 13).inv + (2 ^ 2 : ZMod 13).inv + (2 ^ 3 : ZMod 13).inv + (2 ^ 4 : ZMod 13).inv + (2 ^ 5 : ZMod 13).inv + (2 ^ 6 : ZMod 13).inv = 2 := by
  -- Note: the usage of decide here can be replaced by hand computation
  -- 2 ^ 6 = -1 mod 13
  have h0 : (-2 ^ 6 : ZMod 13) = 1 := by decide
  -- Thus 2 ^ k = (-1) ^ (6 - k) mod 13
  have h1 : (2 ^ 1 : ZMod 13).inv = -2 ^ 5 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [show (2 ^ 1 : ZMod 13) * -2 ^ 5 = -2 ^ 6 by ring]
    exact h0
  have h2 : (2 ^ 2 : ZMod 13).inv = -2 ^ 4 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [show (2 ^ 2 : ZMod 13) * -2 ^ 4 = -2 ^ 6 by ring]
    exact h0
  have h3 : (2 ^ 3 : ZMod 13).inv = -2 ^ 3 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [show (2 ^ 3 : ZMod 13) * -2 ^ 3 = -2 ^ 6 by ring]
    exact h0
  have h4 : (2 ^ 4 : ZMod 13).inv = -2 ^ 2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [show (2 ^ 4 : ZMod 13) * -2 ^ 2 = -2 ^ 6 by ring]
    exact h0
  have h5 : (2 ^ 5 : ZMod 13).inv = -2 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [show (2 ^ 5 : ZMod 13) * -2 = -2 ^ 6 by ring]
    exact h0
  have h6 : (2 ^ 6 : ZMod 13).inv = -1 := by
    apply ZMod.inv_eq_of_mul_eq_one
    rw [show (2 ^ 6 : ZMod 13) * -1 = -2 ^ 6 by ring]
    exact h0

  -- Sum the geometric series
  rw [h1, h2, h3, h4, h5, h6]
  ring_nf
  decide
