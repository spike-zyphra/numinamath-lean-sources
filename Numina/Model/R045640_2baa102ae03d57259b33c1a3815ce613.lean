import Mathlib
theorem algebra_608520 (a c : ℝ) : (∀ b : ℝ, ∃ x y : ℝ, a * x + b * y = c - 1 ∧ (a + 5) * x + (b + 3) * y = c + 1) ↔ c = 2 * a / 5 + 1:= by
  constructor
  · -- Assume that ∀ b : ℝ, ∃ x y : ℝ, a * x + b * y = c - 1 ∧ (a + 5) * x + (b + 3) * y = c + 1, prove that c = 2 * a / 5 + 1
    intro h
    have h2 := h (3 * a / 5)
    rcases h2 with ⟨x2, y2, h2eq1, h2eq2⟩
    -- Subtraction of the second and first equation gives $5x_2 + 3y_2 = 2$.
    have eq2 : (a + 5) * x2 + ((3 * a / 5) + 3) * y2 - (a * x2 + (3 * a / 5) * y2) = (c + 1) - (c - 1) := by
      linarith [h2eq1, h2eq2]
    have eq5 : 5 * x2 + 3 * y2 = 2 := by
      have eq3 : (a + 5) * x2 + ((3 * a / 5) + 3) * y2 - (a * x2 + (3 * a / 5) * y2) = 5 * x2 + 3 * y2 := by
          ring
      have eq4 : (c + 1) - (c - 1) = 2 := by
          ring
      linarith [eq2, eq3, eq4]
    have eq6 : a * x2 + (3 * a / 5) * y2 = c - 1 := by
      linarith [h2eq1]
    have eq7 : 3 * y2 = 2 - 5 * x2 := by
      linarith [eq5]
    have eq8 : y2 = (2 - 5 * x2) / 3 := by
      linarith [eq7]
    rw [eq8] at eq6
    have eq9 : a * x2 + (3 * a / 5) * ((2 - 5 * x2) / 3) = c - 1 := by 
      linarith [eq6]
    have eq11 : a * x2 + (3 * a / 5) * ((2 - 5 * x2) / 3) = 2 * a / 5 := by
      ring_nf
    -- Use equation 9 to solve.
    linarith [eq9, eq11]
  · -- Now prove the reverse, given c = 2a/5 + 1, prove ∀ b, ∃ x y...
    intro h b 
    use (2 / 5), (0)
    constructor
    · -- Check the first equation
      have h1 : c = 2 * a / 5 + 1 := by
        linarith [h]
      rw [show c - 1 = 2 * a / 5 by linarith [h1] ]
      ring_nf
    · -- Check the second equation
      have h1 : c = 2 * a / 5 + 1 := by
        linarith [h]
      rw [show c + 1 = 2 * a / 5 + 2 by linarith [h1] ]
      ring_nf