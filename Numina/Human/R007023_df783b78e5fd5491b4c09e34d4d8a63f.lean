import Mathlib

/- $4 \cdot 128$ Find the relationship between the coefficients $a, b, c$ for the system of equations to have real solutions:

$$

\left\{\begin{array}{l}
a x^{2}+b x+c=0, \\
b x^{2}+c x+a=0, \\
c x^{2}+a x+b=0 .
\end{array}\right.

$$
 -/
theorem algebra_192279 (a b c : ℝ) (ha : a ≠ 0)
(h1 : ∃ x : ℝ, a * x ^ 2 + b * x + c = 0 ∧ b * x ^ 2 + c * x + a = 0 ∧ c * x ^ 2 + a * x + b = 0) :
    b + c + a = 0 := by
        rcases h1 with ⟨x, h⟩
        rcases h with ⟨h_1, h_2, h_3⟩
        --Add the three equations together and get zero.
        have h_4 : a * x ^ 2 + b * x + c + b * x ^ 2 + c * x + a + c * x ^ 2 + a * x + b = 0 := by
            rw [h_1, zero_add]
            rw [h_2, zero_add]
            rw [h_3]
        --Factor out a + b + c.
        have h_5 : a * x ^ 2 + b * x + c + b * x ^ 2 + c * x + a + c * x ^ 2 + a * x + b =
                        (a + b + c) * (x^2 + x + 1) := by ring
        --Show that x^2 + x + 1 is never zero.
        have h_6 : x^2 + x + 1 ≠ 0 := by
            have h' : ∀ x : ℝ, x ^ 2 + x + 1 > 0 := by
                intro x
                -- Complete the square: x² + x + 1 = (x + 1/2)^2 + 3/4
                calc
                x ^ 2 + x + 1 = (x + 1/2) ^ 2 + 3/4 := by ring
                _ > 0 := by
                    apply add_pos_of_nonneg_of_pos
                    · exact sq_nonneg (x + 1 / 2)
                    · norm_num
            exact ne_of_gt (h' x)
        --Two cases now.
        simp_all only [ne_eq, zero_add, zero_eq_mul]
        cases h_5 with
        | inl h => linarith
        | inr h_4 => contradiction