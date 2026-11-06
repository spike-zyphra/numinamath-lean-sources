import Mathlib

open Real

/-- Let $a$ and $b$ be positive real numbers with $a\ge b$. Let $\rho$ be the maximum possible value of $\frac {a}{b}$ for which the system of equations $$
a^2 + y^2 = b^2 + x^2 = (a - x)^2 + (b - y)^2
$$has a solution in $(x,y)$ satisfying $0\le x < a$ and $0\le y < b$.  Find $\rho^2.$-/
theorem intermediate_algebra_4083 : (∀ (a b : ℝ), b ≤ a → (∃ x : ℝ, ∃ y : ℝ, 0 ≤ x ∧ x < a ∧ 0 ≤ y ∧ y < b ∧
              a^2 + y^2 = b^2 + x^2 ∧ b^2 + x^2 = (a-x)^2 + (b-y)^2) → (a/b)^2 ≤ 4/3) ∧
              ∃ a : ℝ, ∃ b : ℝ, b ≤ a ∧ (∃ x : ℝ, ∃ y : ℝ, 0 ≤ x ∧ x < a ∧ 0 ≤ y ∧ y < b ∧
              a^2 + y^2 = b^2 + x^2 ∧ b^2 + x^2 = (a-x)^2 + (b-y)^2) ∧ (a/b)^2 = 4/3
              := by
  constructor
  · intro a b _ ⟨x,⟨y,⟨hxnonneg,⟨hxa,⟨hynonneg,⟨hyb,⟨h₁,h₂⟩⟩⟩⟩⟩⟩⟩
    -- Because $0 \leq y < b$, we get $0 \leq 2by - y^2$.
    have : 0 ≤ 2*b*y - y^2 := by
      nlinarith
    -- Because $a^2 \leq a^2 +y^2 = b^2 + x^2 \leq b^2 + (a^2)/4$, so $3/4 * a^2 ≤ b^2$.
    have : 3/4 * a^2 ≤ b^2 := by
      nlinarith
    -- So we can get the maximum possible value of $\frac {a^2} {b^2}$ is $\frac 4 3$.
    norm_num
    have hb : 0 < b := by linarith
    field_simp [hb]
    rw [div_le_iff]
    linarith
    exact sq_pos_of_pos hb
  · -- Equality occurs when $a = 1, b = \frac {\sqrt3} 2, x = 1/2, and y =0$.
    use 1; use √3 / 2
    constructor
    · rw [div_le_one (show 0 < (2 : ℝ) by norm_num)]
      rw [Real.sqrt_le_iff, (show 2^2 = (4 : ℝ) by norm_num)]
      constructor <;> linarith
    · constructor
      · use 1 / 2; use 0
        simp_all
        constructor
        · apply inv_lt_one (show 1 < (2 : ℝ) by norm_num)
        · field_simp
          norm_num
      · rw [div_pow 1,one_pow, div_pow √3, sq_sqrt,one_div_div]
        norm_num; linarith
