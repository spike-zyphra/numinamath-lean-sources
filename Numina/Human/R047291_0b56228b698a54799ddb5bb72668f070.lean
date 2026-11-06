import Mathlib

/- Given a quadratic equation in $x$, $kx^2-6x+9=0$, has two distinct real roots, find the range of values for $k$. -/
theorem algebra_9047 : {k | k ≠ 0 ∧ ∃ x₁ x₂ : ℝ,
    k * x₁ ^ 2 - 6 * x₁ + 9 = 0 ∧ k * x₂ ^ 2 - 6 * x₂ + 9 = 0 ∧ x₁ ≠ x₂} = {k | k < 1 ∧ k ≠ 0} := by
  ext k
  simp
  constructor <;> intro ⟨h1, h2⟩

  . -- In this part, we prove that if a quadratic function has two roots, then the discriminant is positive
    refine ⟨?_, h1⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, h2⟩ := h2
    replace h2 : x₁ - x₂ ≠ 0 := by linarith (config := {splitNe := true})
    have h3 : (x₁ - x₂) ^ 2 > 0 := pow_two_pos_of_ne_zero h2

    -- Substract the two equations
    have h4 : (x₁ - x₂) * (k * (x₁ + x₂) - 6) = 0 := by linarith
    have h5 : k * (x₁ + x₂) - 6 = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero h2 h4

    -- Add the two equations
    have h6 : k^2 * (x₁^2 + x₂^2) - 36 + 18 * k = 0 := by nlinarith (config := {splitNe := true})

    -- x₁^2 + x₂^2 ≥ (x₁ + x₂)^2 / 2
    have h7 : (k * x₁ - k * x₂)^2 > 0 := pow_two_pos_of_ne_zero (by nlinarith)
    have h8 : k^2 * (x₁^2 + x₂^2) > 18 := by nlinarith
    linarith

  . refine ⟨h2, ?_⟩

    -- Quadratic formula
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

    -- Use the formula to solve the quadratic equation, where the discriminant is positive
    specialize formula k (-6) 9 h2 (by linarith)
    simp at formula
    conv at formula =>
      intro x
      rw [(by ring : k * x ^ 2 + -(6 * x) + 9 = k * x ^ 2 - 6 * x + 9)]
    have h3 : √(6 ^ 2 - 4 * k * 9) > 0 := Real.sqrt_pos_of_pos (by linarith)

    -- Plug in the two roots
    use (6 + √(6 ^ 2 - 4 * k * 9)) / (2 * k)
    refine ⟨(formula _).2 (Or.inl rfl), ?_⟩
    use (6 - √(6 ^ 2 - 4 * k * 9)) / (2 * k)
    refine ⟨(formula _).2 (Or.inr rfl), ?_⟩

    -- Prove they are distinct
    field_simp
    linarith
