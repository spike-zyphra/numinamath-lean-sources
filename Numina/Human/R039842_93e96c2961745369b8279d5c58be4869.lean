import Mathlib

open Real

/- 8. Prove that for all $a, b, c>0$ it holds that


$$

\frac{a^{2}}{b^{3} c}-\frac{a}{b^{2}} \geq \frac{c}{b}-\frac{c^{2}}{a}

$$


In what case does equality hold? -/
theorem inequalities_178178 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 / (b^3 * c) - a / b^2 ≥ c / b - c^2 / a := by

        --Show (a^2 - b^2 * c^2) * (a - b * c) ≥ 0. We use difference of two squares.
        have h₁ : (a^2 - b^2 * c^2) * (a - b * c) ≥ 0 := by
            have : (a^2 - b^2 * c^2) * (a - b * c)= (a + b * c) * (a - b * c)^2 := by ring
            rw [this]
            positivity

        --(a^2 - b^2 * c^2) * (a - b * c) = a^2 * (a - b * c) - c^2 * b^2 * (a - b * c).
        have h₂ : (a^2 - b^2 * c^2) * (a - b * c) = a^2 * (a - b * c) - c^2 * b^2 * (a - b * c) := by ring

        --Show a^2 * (a - b * c) - c^2 * b^2 * (a - b * c) = a^3 - a * c^2 * b^2 - a^2 * b * c + c^3 * b^3.
        have h₃ :  a^2 * (a - b * c) - c^2 * b^2 * (a - b * c) = a^3 - a * c^2 * b^2 - a^2 * b * c + c^3 * b^3 := by ring

        --Show a^3 - a * c^2 * b^2 - a^2 * b * c + c^3 * b^3 = a^3 - a^2 * b * c - a * c^2 * b^2 + c^3 * b^3.
        have h₄ : a^3 - a * c^2 * b^2 - a^2 * b * c + c^3 * b^3 = a^3 - a^2 * b * c - a * c^2 * b^2 + c^3 * b^3 := by ring

        --Show a^3 - a^2 * b * c - a * c^2 * b^2 + c^3 * b^3
        have h₅ :  a^3 - a^2 * b * c - a * c^2 * b^2 + c^3 * b^3 =
            a * b^3 * c * (a^2 / (b^3 * c) - a / b^2 - c / b + c^2 / a) := by
                field_simp
                ring

        --Show a * b^3 * c * (a^2 / (b^3 * c) - a / b^2 - c / b + c^2 / a) ≥ 0
        have h₆ : a * b^3 * c * (a^2 / (b^3 * c) - a / b^2 - c / b + c^2 / a) ≥ 0 := by linarith

        --Show a^2 / (b^3 * c) - a / b^2 - c / b + c^2 / a) ≥ 0. We argue by way of contradiction.
        have h₇ : (a^2 / (b^3 * c) - a / b^2 - c / b + c^2 / a) ≥ 0 := by
            by_contra h₇
            push_neg at h₇
            have h₇1 : a * b^3 * c > 0 := by positivity
            have h₇2 : a * b^3 * c * (a^2 / (b^3 * c) - a / b^2 - c / b + c^2 / a) < 0 := by
                exact mul_neg_of_pos_of_neg h₇1 h₇
            have h₇3 : a * b^3 * c * (a^2 / (b^3 * c) - a / b^2 - c / b + c^2 / a) ≥ 0 := by exact h₆
            have : 0 < 0 := by linarith
            contradiction

        --Now, `linarith` closes the goal.
        linarith