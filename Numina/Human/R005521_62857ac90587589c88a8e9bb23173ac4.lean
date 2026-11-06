import Mathlib
open Rat

/-Suppose that in every room, Mario randomly picks a door to walk through. What is the expected number of doors (not including Mario's initial entrance to the first room) through which Mario will pass before he reaches Bowser's level?-/

-- Define the problem using variables for the expected values.
variable (E₁ E₂ : ℚ)

-- From Room 1: 1 door is passed, then with 3/4 probability you are back in Room 1
-- (requiring E₁ more doors on average) and with 1/4 probability you are in Room 2
-- (requiring E₂ more doors on average).
def equation_for_E1 : Prop :=
  E₁ = 1 + (3 / 4) * E₁ + (1 / 4) * E₂

-- From Room 2: 1 door is passed, then with 3/4 probability you are in Room 1
-- (requiring E₁ more doors on average) and with 1/4 probability you are in Room 3.
-- Since the expected future doors from Room 3 is E₃ = 0, this term is (1/4) * 0 = 0.
def equation_for_E2 : Prop :=
  E₂ = 1 + (3 / 4) * E₁

-- If E₁ and E₂ satisfy the two equations, then E₁ must be 20.
theorem combinatorics_608620 (h1 : equation_for_E1 E₁ E₂) (h2 : equation_for_E2 E₁ E₂) :
  E₁ = 20 :=
by

  have h1_rearranged : E₁ - E₂ = 4 := by
    rw [equation_for_E1] at h1
    linarith [h1]


  have h2_rearranged : -3 * E₁ + 4 * E₂ = 4 := by
    rw [equation_for_E2] at h2
    linarith [h2]

  linarith [h1_rearranged, h2_rearranged]

