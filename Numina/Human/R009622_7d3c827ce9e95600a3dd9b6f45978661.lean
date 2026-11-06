import Mathlib

/- Solve the quadratic equation $2x^2 - 5x + 2 = 0$ using the quadratic formula. -/
theorem algebra_9278 (x : ℝ) : 2*x^2-5*x+2=0 ↔
    x = 2 ∨ x = 1/2 := by
  -- We first prove the formula for solving quadratic equations
  -- $ax^{2}+bx+c=0$ where $a \neq 0$ and $b^{2}-4ac \geq 0$
  -- has solutions $x=\frac{-b \pm \sqrt{b^{2}-4ac}}{2a}$
  have formula (a b c) (ha : a ≠ 0) (hd : b^2 - 4*a*c ≥ 0) (x : ℝ) : a*x^2 + b*x + c = 0 ↔ x = (-b + √(b^2 - 4*a*c)) / (2*a) ∨ x = (-b - √(b^2 - 4*a*c)) / (2*a) := by

    -- a*x^2 + b*x + c = 0 ↔ (x + b/(2*a))^2 = (b^2 - 4*a*c)/((2*a)^2)
    have h : a*x^2 + b*x + c = 0 ↔ (x + b/(2*a))^2 = (b^2 - 4*a*c)/((2*a)^2) := by
      -- Both implications can be proved by cancelling the denominators and nlinarith
      constructor <;> intro h
      . field_simp [ha]
        nlinarith (config := {splitNe := True})
      . field_simp [ha] at h
        nlinarith (config := {splitNe := True})

    -- Rewrite the equation using the above lemma
    -- And take square root on both sides
    rw [h]
    nth_rewrite 1 [←Real.sq_sqrt hd]
    rw [←div_pow, sq_eq_sq_iff_eq_or_eq_neg]

    -- Now the goal is (p₁ ∨ q₁) ↔ (p₂ ∨ q₂)
    -- Where p₁ and p₂ are equivalent which can be proved by field_simp and linarith, the same for q₁ and q₂

    -- Split the iff into two implications
    constructor <;> intro h <;>
    -- Split the cases for _ ∨ _
    obtain h | h := h <;>
    -- Choose correct subgoal for the 4 cases
    [left; right; left; right] <;>
    -- field_simp and linarith
    field_simp [ha] at h ⊢ <;> linarith

  -- Now we can use the formula to solve the equation
  specialize formula 2 (-5) 2 (by norm_num) (by norm_num) x
  -- Simplify the two roots
  have ⟨h1, h2⟩ : (- -5 + √((-5) ^ 2 - 4 * 2 * 2)) / (2 * 2) = 2 ∧ (- -5 - √((-5) ^ 2 - 4 * 2 * 2)) / (2 * 2) = 1/2 := by
    constructor
    all_goals
      norm_num
      simp [(by norm_num : √9 = √(3^2))]
      norm_num
  -- Rewrite the equation to match the form of the formula
  have h3 : 2 * x ^ 2 + -5 * x + 2 = 2 * x ^ 2 - 5 * x + 2 := by ring
  rwa [h1, h2, h3] at formula
