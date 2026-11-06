import Mathlib
/- Let $x, y, z$ be real numbers (not necessarily positive) such that $x^{4}+y^{4}+z^{4}+x y z=4$. Prove that $x \leq 2$ and  $$ \sqrt{2-x} \geq \frac{y+z}{2} $$ -/
theorem algebra_605149 (x y z : ℝ) (h : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z = 4) :
    x ≤ 2 ∧ √(2 - x) ≥ (y + z) / 2 := by
        -- First part: Prove x ≤ 2
        have h1 : x ≤ 2:= by
            -- Use several non-negativity facts
            have g1 : (x ^ 2 - 2 * y ^ 2) ^ 2 ≥ 0:= by positivity
            have g2 : (z ^ 2 - 1) ^ 2 ≥ 0:= by positivity
            have g3 : (2 * x * y + z) ^ 2 ≥ 0:= by positivity
            have g4 : z ^ 2 ≥ 0:= by positivity
            -- Key inequality: x^4 ≤ 20/3
            have g5 : x ^ 4 ≤ 20 / 3:= by linarith
            clear g1 g2 g3 g4
            -- Proof by contradiction
            by_contra H
            simp at H
            -- If x > 2, then x^2 > 4
            replace H : x ^ 2 > 4:= by nlinarith only [H]
            -- Therefore x^4 > 16, contradicting x^4 ≤ 20/3
            replace H : x ^ 4 > 16:= by nlinarith only [H]
            linarith

        simp [h1]
        -- Second part: Prove √(2-x) ≥ (y+z)/2
        -- We'll first prove ((y+z)/2)^2 ≤ 2-x
        have h2 : ((y + z) / 2) ^ 2 ≤ 2 - x:= by
            by_contra H
            simp at H
            -- More non-negativity facts
            have g1 : (x - 1) ^ 2 * (2 + (x + 1) ^ 2) ≥ 0:= by positivity
            have g2 : (y ^ 2 - 1) ^ 2 ≥ 0:= by positivity
            have g3 : (z ^ 2 - 1) ^ 2 ≥ 0:= by positivity
            -- Key inequality relating y*z and y^4 + z^4
            have g4 : (2 - x) * (y * z) > (y ^ 4 + z ^ 4) / 2:= by linarith
            clear g1 g2 g3
            -- Prove y*z > 0 by contradiction
            have g1 : y * z > 0:= by
                by_contra H1
                simp at H1
                replace H1 : -y * z ≥ 0:= by linarith
                replace h1 : 2 - x ≥ 0:= by linarith
                replace H1 : (2 - x) * (-y * z) ≥ 0:= by positivity
                have g1 : y ^ 4 + z ^ 4 ≥ 0:= by positivity
                linarith
            -- Chain of inequalities to reach contradiction
            replace g4 : 2 - x > ((y ^ 4 + z ^ 4) / 2) / (y * z):= by exact (div_lt_iff₀ g1).mpr g4
            have g2 : ((y ^ 4 + z ^ 4) / 2) / (y * z) ≥ ((y + z) / 2) ^ 2:= by
                suffices ((y ^ 4 + z ^ 4) / 2) ≥ ((y + z) / 2) ^ 2 * (y * z) by exact (le_div_iff₀ g1).mpr this
                have g5 : (y ^ 2 - z ^ 2) ^ 2 ≥ 0:= by positivity
                have g6 : (y ^ 2 + z ^ 2) * (y - z) ^ 2 ≥ 0:= by positivity
                linarith
            linarith

        -- Final steps: Convert squared inequality to the desired form
        replace h1 : 2 - x ≥ 0:= by linarith
        rw [show 2 - x = (√(2 - x)) ^ 2 by exact Eq.symm (Real.sq_sqrt h1)] at h2
        replace h2 : |(y + z) / 2| ≤ |√(2 - x)|:= by exact sq_le_sq.mp h2
        rw [show |√(2 - x)| = √(2 - x) by simp] at h2
        have h3 : |(y + z) / 2| ≥ (y + z) / 2:= by exact le_abs_self ((y + z) / 2)
        linarith
