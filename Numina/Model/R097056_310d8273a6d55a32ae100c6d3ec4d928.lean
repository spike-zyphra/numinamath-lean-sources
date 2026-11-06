import Mathlib

theorem algebra_12586 (c : ℝ) :
    (c = -3) ↔ (∀ x y, (x + 3)^2 + (y - 2)^2 = 4^2 ↔
      x^2 + 6 * x + y^2 - 4 * y + c = 0) := by
  constructor
  · -- Forward direction: Prove that c = -3 implies the equivalence of the equations
    intro hc
    intro x y
    subst hc
    constructor
    · -- Forward direction: circle equation implies original equation
      intro h
      nlinarith
    · -- Backward direction: original equation implies circle equation
      intro h
      nlinarith
  · -- Backward direction: Prove that the equivalence implies c = -3
    intro h
    have h1 := h (-3) 6
    norm_num at h1
    linarith