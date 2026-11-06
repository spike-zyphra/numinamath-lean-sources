import Mathlib
/-Given the equation about x:
(a^2 - 1) * (x / (x - 1))^2 - (2 * a + 7) * (x / (x - 1)) + 1 = 0 has real roots.
(1) Find the range of values for a
(2) if the two real roots of the original equation are x1 and x2 and 
x1/(x1-1) + x2/(x2-1) = 3/11, find the value of a -/
theorem algebra_308669 (a : ℝ) (h : ∃ x1 x2 : ℝ, x1 ≠ 1 ∧ x2 ≠ 1 ∧ 
(a^2 - 1) * (x1 / (x1 - 1))^2 - (2 * a + 7) * (x1 / (x1 - 1)) + 1 = 0 ∧ 
(a^2 - 1) * (x2 / (x2 - 1))^2 - (2 * a + 7) * (x2 / (x2 - 1)) + 1 = 0 ∧ (x1 / (x1 - 1)) + (x2 / (x2 - 1)) = 3 / 11) :
    a ≥ -53 / 28 := by
        obtain ⟨x1, x2, hx1, hx2, h1, h2, h3⟩ := h
        -- we need to verify the denominator is not zero --
        have h4 : x1 - 1 ≠ 0 := by
            intro h5
            have : x1 = 1 := by linarith
            contradiction
        -- we then prove the result step by step --
        have h6 : (2 * a + 7) ^ 2 - 4 * (a^2 - 1) ≥ 0 := by
            have h7 : (2 * (a^2 - 1) * (x1 / (x1 - 1)) - (2 * a + 7)) ^ 2 ≥ 0 := by
                apply sq_nonneg
            have h8 : (2 * (a^2 - 1) * (x1 / (x1 - 1)) - (2 * a + 7)) ^ 2 = (2 * a + 7) ^ 2 - 4 * (a^2 - 1) := by
                have eq1 : (2 * (a^2 - 1) * (x1 / (x1 - 1)) - (2 * a + 7)) ^ 2 = 
                    4 * (a^2 - 1) ^ 2 * (x1 / (x1 - 1)) ^ 2 - 4 * (a^2 - 1) * (2 * a + 7) * (x1 / (x1 - 1)) + (2 * a + 7) ^ 2 := by ring
                have eq2 : 4 * (a^2 - 1) ^ 2 * (x1 / (x1 - 1)) ^ 2 - 4 * (a^2 - 1) * (2 * a + 7) * (x1 / (x1 - 1)) + (2 * a + 7) ^ 2 = (2 * a + 7) ^ 2 - 4 * (a^2 - 1) := by
                    have eq3 : 4 * (a^2 - 1) ^ 2 * (x1 / (x1 - 1)) ^ 2 - 4 * (a^2 - 1) * (2 * a + 7) * (x1 / (x1 - 1)) + (2 * a + 7) ^ 2 = 
                        (4 * (a^2 - 1) ^ 2 * (x1 / (x1 - 1)) ^ 2 - 4 * (a^2 - 1) * (2 * a + 7) * (x1 / (x1 - 1)) + 4 * (a^2 - 1)) + (2 * a + 7) ^ 2 - 4 * (a^2 - 1) := by ring
                    have eq4 : 4 * (a^2 - 1) ^ 2 * (x1 / (x1 - 1)) ^ 2 - 4 * (a^2 - 1) * (2 * a + 7) * (x1 / (x1 - 1)) + 4 * (a^2 - 1) = 0 := by
                        have eq5 : 4 * (a^2 - 1) ^ 2 * (x1 / (x1 - 1)) ^ 2 - 4 * (a^2 - 1) * (2 * a + 7) * (x1 / (x1 - 1)) + 4 * (a^2 - 1) = 
                            4 * ((a^2 - 1) * (x1 / (x1 - 1)) ^ 2 - (2 * a + 7) * (x1 / (x1 - 1)) + 1) * (a^2 - 1) := by 
                            ring
                        rw [eq5]
                        rw [h1]
                        ring
                    linarith [eq3, eq4]
                linarith [eq1, eq2]
            nlinarith
        nlinarith [sq_nonneg (a + 53 / 28)]