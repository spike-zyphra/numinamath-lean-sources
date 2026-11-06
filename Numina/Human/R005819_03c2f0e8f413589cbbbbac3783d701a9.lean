import Mathlib

/-A polynomial P with integer coefficients is called tricky if it has 4 as a root.
A polynomial is called teeny if it has degree at most 1 and integer coefficients between -7 and 7 ,
inclusive. How many nonzero tricky teeny polynomials are there?-/

-- note that the conditions are equivalent to P = a(x-4), and a ≠ 0, -7 ≤ a ≤ 7, -7 ≤ 4a ≤ 7 --
theorem algebra_610058: {a: ℤ | a ≠ 0 ∧ -7 ≤ a ∧ a ≤ 7 ∧ -7 ≤ 4 * a ∧ 4 * a ≤ 7}.encard = 2 := by

-- the set is indeed {-1,1} --
  have set_eq: {a: ℤ | a ≠ 0 ∧ -7 ≤ a ∧ a ≤ 7 ∧ -7 ≤ 4 * a ∧ 4 * a ≤ 7} = {1, -1} := by
    ext a
    constructor
    -- the forward direction
    . intro ha
      simp at ha
      rcases ha with ⟨ne_0,ba1,ba2,ba3,ba4⟩
      simp
      omega
      -- the backward direction
    . intro ha
      simp at ha
      simp
      omega
-- counting the card --
  rw [set_eq]
  simp [Set.encard]