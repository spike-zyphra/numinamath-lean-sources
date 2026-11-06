import Mathlib
/- Montrer que pour tous réels $\mathrm{a}, \mathrm{b}, \mathrm{c}$ strictement positifs:

$$
\frac{b c}{a^{2}+2 b c}+\frac{c a}{b^{2}+2 c a}+\frac{a b}{c^{2}+2 a b} \leqslant 1 \leqslant \frac{a^{2}}{a^{2}+2 b c}+\frac{b^{2}}{b^{2}+2 c a}+\frac{c^{2}}{c^{2}+2 a b}
$$ -/
theorem inequalities_607359 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) +
    a * b / (c ^ 2 + 2 * a * b) ≤ 1 ∧ 1 ≤ a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) := by
        -- Let G be the sum of three squared terms (right side of inequality)
        set G:= a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) with hG
        -- Let H be the sum of three product terms (left side of inequality)
        set H:= b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) + a * b / (c ^ 2 + 2 * a * b) with hH
        clear_value G H
        -- Key insight: G + 2H = 3
        have h1 : G + 2 * H = 3:= by
            rw [hG, hH]
            field_simp
            linarith
        -- Prove G ≥ 1 using the fact that squared differences are non-negative
        have h2 : G ≥ 1:= by
            rw [hG]
            -- Show that denominators can be bounded using (b-c)²≥0
            have g1 : a ^ 2 + 2 * b * c ≤ a ^ 2 + b ^ 2 + c ^ 2:= by
                have g1 : (b - c) ^ 2 ≥ 0:= by positivity
                linarith only [g1]
            -- Similar bound using (c-a)²≥0
            have g2 : b ^ 2 + 2 * c * a ≤ b ^ 2 + c ^ 2 + a ^ 2:= by
                have g2 : (c - a) ^ 2 ≥ 0:= by positivity
                linarith only [g2]
            -- Similar bound using (a-b)²≥0
            have g3 : c ^ 2 + 2 * a * b ≤ c ^ 2 + a ^ 2 + b ^ 2:= by
                have g3 : (a - b) ^ 2 ≥ 0:= by positivity
                linarith only [g3]
            -- Apply division inequality to each term
            replace g1 : a ^ 2 / (a ^ 2 + 2 * b * c) ≥ a ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2):= by refine div_le_div_of_nonneg_left (by positivity) (by positivity) g1
            replace g2 : b ^ 2 / (b ^ 2 + 2 * c * a) ≥ b ^ 2 / (b ^ 2 + c ^ 2 + a ^ 2):= by refine div_le_div_of_nonneg_left (by positivity) (by positivity) g2
            replace g3 : c ^ 2 / (c ^ 2 + 2 * a * b) ≥ c ^ 2 / (c ^ 2 + a ^ 2 + b ^ 2):= by refine div_le_div_of_nonneg_left (by positivity) (by positivity) g3
            -- The sum of these three fractions equals 1
            suffices a ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) + b ^ 2 / (b ^ 2 + c ^ 2 + a ^ 2) + c ^ 2 / (c ^ 2 + a ^ 2 + b ^ 2) = 1 by linarith
            field_simp
            linarith
        -- Complete the proof using G + 2H = 3 and G ≥ 1
        constructor
        all_goals
        linarith
