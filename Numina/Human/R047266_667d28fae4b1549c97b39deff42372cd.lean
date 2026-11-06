import Mathlib
open Real

/-
$\square$
Example 20 Let $a \geqslant b \geqslant c \geqslant 0$, and $a+b+c=3$, prove: $a b^{2}+b c^{2}+c a^{2} \leqslant \frac{27}{8}$. And determine the condition for equality. (2002 Hong Kong Mathematical Olympiad Problem)
-/
theorem inequalities_600871 (a b c : ℝ) (h₀ : 0 ≤ c) (h₁ : c ≤ b) (h₂ : b ≤ a)
    (h₃ : a + b + c = 3) :
    a * b^2 + b * c^2 + c * a^2 ≤ 27 / 8 ∧
    (a * b^2 + b * c^2 + c * a^2 = 27 / 8 ↔ a = 3 / 2 ∧ b = 3 / 2 ∧ c = 0) := by
  constructor
  · -- First, we prove the inequality $a * b^2 + b * c^2 + c * a^2 \leq 27/8$
    nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (b - c),
              h₃, mul_self_nonneg (a - 3 / 2), mul_self_nonneg (b - 3 / 2), mul_self_nonneg (c),
              sq_nonneg (a + b + c - 3), sq_nonneg (a - b), sq_nonneg (b - c)]
  · -- Now, we prove the equality condition
    constructor
    · -- Forward direction: if $a * b^2 + b * c^2 + c * a^2 = 27/8$, then $a = 3/2 \land b = 3/2 \land c = 0$
      intro h_eq
      have h4 : c = 0 := by
        nlinarith [sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (b - c),
                  h₃, h_eq]
      have h5 : a + b = 3 := by linarith
      have h6 : a = 3 / 2 := by
        have : (a - 3 / 2) ^ 2 ≥ 0 := sq_nonneg (a - 3 / 2)
        have : (b - 3 / 2) ^ 2 ≥ 0 := sq_nonneg (b - 3 / 2)
        nlinarith
      have h7 : b = 3 / 2 := by linarith
      exact ⟨h6, h7, h4⟩
    · -- Backward direction: if $a = 3/2 \land b = 3/2 \land c = 0$, then $a * b^2 + b * c^2 + c * a^2 = 27/8$
      rintro ⟨ha, hb, hc⟩
      rw [ha, hb, hc]
      norm_num