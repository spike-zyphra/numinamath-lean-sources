import Mathlib

open Real

/- 5. Given that $x, y$ are real numbers, and satisfy $3 x^{2}+2 y^{2} \leqslant 6$, prove: $2 x+y \leqslant \sqrt{11}$. -/
theorem inequalities_221557 (x y : ℝ) (h : 3 * x ^ 2 + 2 * y ^ 2 ≤ 6) :
    2 * x + y ≤ sqrt 11 := by

        --Let a = 2/sqrt(3), b = sqrt(3)x, c = 1/sqrt(2), d = sqrt(2)*y
        set a := 2 / Real.sqrt 3
        set b := 1 / Real.sqrt 2
        set c := Real.sqrt 3 * x
        set d := Real.sqrt 2 * y

        --Show that (a * c + b * d)^2 ≤ (a^2 + b^2) * (c^2 + d^2); this is Cauchy-Schwarz for i = 2.
        have h₁ : (a * c + b * d)^2 ≤ (a^2 + b^2) * (c^2 + d^2) := by

            --Show (a^2 + b^2) * (c^2 + d^2) - (a * c + b * d)^2 = (a * d - b * c)^2.
            have h1 : (a^2 + b^2) * (c^2 + d^2) - (a * c + b * d)^2 = (a * d - b * c)^2 := by
                ring
            --Show (a * d - b * c)^2 ≥ 0.
            have h2 : (a * d - b * c)^2 ≥ 0 := by
                exact sq_nonneg (a * d - b * c)
            --`linarith` now closes the goal.
            linarith

        --Show a^2 + b^2 = 11 / 6. We use `calc`
        have h₂ : a^2 + b^2 = 11 / 6 := by
            calc
                _ = (2 / Real.sqrt 3)^2 + (1 / Real.sqrt 2)^2 := by exact rfl
                _ = 2^2 / (Real.sqrt 3)^2 + 1^2 / (Real.sqrt 2)^2 := by
                    rw [div_pow]
                    rw [div_pow]
                _ = 4 / 3 + 1 / 2 := by norm_num
                _ = 11 / 6 := by norm_num

        --Show (a * c + b * d)^2 = (2 * x + y)^2. We use `calc`.
        have h₃ : (a * c + b * d)^2 = (2 * x + y)^2 := by
            calc
                _ = ((2 / Real.sqrt 3) * (Real.sqrt 3 * x) + (1 / Real.sqrt 2) * (Real.sqrt 2 * y))^2 := by exact
                  rfl
                _ = (2 * x + y)^2 := by
                    simp
                    rw [← mul_assoc]
                    simp

        --Show c^2 + d^2 = 3 * x ^2 + 2 * y^2. We use `calc`.
        have h₄ : c^2 + d^2 = 3 * x ^2 + 2 * y^2 := by
            calc
                _ = (Real.sqrt 3 * x)^2 + (Real.sqrt 2 * y)^2 := by exact rfl
                _ = (Real.sqrt 3)^2 * x^2 + (Real.sqrt 2)^2 * y^2 := by
                    rw [mul_pow]
                    rw [mul_pow]
                _ = 3 * x ^2 + 2 * y^2 := by
                    rw [sq_sqrt]
                    rw [sq_sqrt]
                    norm_num
                    norm_num

        --Rewrite h₂, h₃, and h₄ at h₁.
        rw [h₂, h₃, h₄] at h₁

        --Show that (2 * x + y) ^ 2 ≤ 11 / 6 * 6 and simplify.
        have h₅ : (2 * x + y) ^ 2 ≤ 11 / 6 * 6 := by
            linarith

        simp at h₅
        exact le_sqrt_of_sq_le h₅