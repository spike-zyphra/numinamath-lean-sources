import Mathlib

theorem number_theory_10813 : (2 * (5 : ZMod 56)⁻¹ + 8 * (11 : ZMod 56)⁻¹) = (50 : ZMod 56) := by
  -- First show that 5⁻¹ is 45
  have h1 : (5 : ZMod 56)⁻¹ = (45 : ZMod 56) := by
    native_decide
  -- First show that 11⁻¹ is 51
  have h2 : (11 : ZMod 56)⁻¹ = (51 : ZMod 56) := by
    native_decide
  rw [h1, h2]
  -- Now the goal is 2 * 45 + 8 * 51 = 50 (mod 56)
  native_decide