import Mathlib
/-Set P ={x | x ^ 2 - 5 * x + 6 = 0}, M={x | m * x - 1 = 0},
then the set of real numbers m that satisfy the condition is
-/
theorem algebra_157393 (m : ℝ) (M : Set ℝ) (hM : M = {x | m * x - 1 = 0}) :
    M ⊆ {x | x ^ 2 - 5 * x + 6 = 0} ↔ m = 1 / 2 ∨ m = 1 / 3 ∨ m = 0 := by
        constructor
        · -- If $M \subseteq \{x \mid x^2 - 5x + 6 = 0\}$, then $m \in \{\frac{1}{2}, \frac{1}{3}, 0\}$
            intro h
            by_cases h1 : m = 0
            · -- When $m = 0$, $M = \{x \mid 0 \cdot x - 1 = 0\} = \emptyset$, which is valid
                right
                right
                exact h1
            · -- When $m \neq 0$
                have h2 : m ≠ 0 := by
                    intro h2
                    contradiction
                have h3 : ∀ x, m * x - 1 = 0 → x ^ 2 - 5 * x + 6 = 0 := by
                    intro x hx
                    have h4 : x ∈ M := by
                        rw [hM]
                        exact hx
                    have h5 : x ∈ {x : ℝ | x ^ 2 - 5 * x + 6 = 0} := h h4
                    exact h5
                have h4 : m * (1 / m) - 1 = 0 := by
                    field_simp [h2]
                have h5 := h3 (1 / m) h4
                have h6 : (1 / m) ^ 2 - 5 * (1 / m) + 6 = 0 := by
                    simpa using h5
                have h7 : 6 * m ^ 2 - 5 * m + 1 = 0 := by
                    have h8 : m ≠ 0 := h2
                    field_simp at h6
                    nlinarith
                have h9 : (3 * m - 1) * (2 * m - 1) = 0 := by
                    linarith
                cases' (mul_eq_zero.mp h9) with h10 h11
                · -- $3m - 1 = 0$
                    right
                    left
                    linarith
                · -- $2m - 1 = 0$
                    left
                    linarith
        · -- If $m \in \{\frac{1}{2}, \frac{1}{3}, 0\}$, then $M \subseteq \{x \mid x^2 - 5x + 6 = 0\}$
            intro h
            rcases h with h1 | h2 | h3
            · -- When $m = \frac{1}{2}$, $M = \{2\}$ and $2 \in \{x \mid x^2 - 5x + 6 = 0\}$
                rw [h1] at hM 
                intro x hx
                rw [hM] at hx
                have h4 : x = 2 := by
                    have h5 : (1 / 2 : ℝ) * x - 1 = 0 := hx
                    linarith
                rw [h4]
                norm_num
            · -- When $m = \frac{1}{3}$, $M = \{3\}$ and $3 \in \{x \mid x^2 - 5x + 6 = 0\}$
                rw [h2] at hM 
                intro x hx
                rw [hM] at hx
                have h4 : x = 3 := by
                    have h5 : (1 / 3 : ℝ) * x - 1 = 0 := hx
                    linarith
                rw [h4]
                norm_num
            · -- When $m = 0$, $M = \emptyset$, so $M \subseteq \{x \mid x^2 - 5x + 6 = 0\}$
                rw [h3] at hM 
                intro x hx
                rw [hM] at hx
                have h4 : 0 * x - 1 = 0 := hx
                have : 0 * x - 1 ≠ 0 := by
                    intro h
                    have h5 : 0 * x = 0 := by
                        simp
                    have h6 : 0 * x = 1 := by linarith
                    linarith
                contradiction