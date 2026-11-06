import Mathlib

/- Given that $2+\sqrt{3}$ is a root of the equation \[x^3 + ax^2 + bx + 10 = 0\]and that $a$ and $b$ are rational numbers, compute $b.$ -/
theorem algebra_12394 (a b : ℚ) (h : (2 + Real.sqrt 3) ^ 3 + a * (2 + Real.sqrt 3) ^ 2 + b * (2 + Real.sqrt 3) + 10 = 0) :
    b = -39 := by
  -- We directly substitute x = 2 + √3 and compute b.
  ring_nf at h
  rw [show Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 by rw [show 3 = 2 + 1 by norm_num]; rw [pow_add]; norm_num] at h
  norm_num at h
  replace h : (7 * a + 2 * b + 36) + (4 * a + b + 15) * Real.sqrt 3 = 0 := by
    ring_nf at h ⊢
    exact h
  -- √3 is irrational.
  have irrational_sqrt_three : Irrational (Real.sqrt (3 : ℕ)) := by
    rw [irrational_sqrt_natCast_iff]
    native_decide -- Decide that 3 is not a square.
  norm_cast at irrational_sqrt_three
  -- We claim that p + q √3 = 0 implies p = q = 0.
  have irrat_linear_combination (p q : ℚ) : p + q * Real.sqrt 3 = 0 → p = 0 ∧ q = 0 := by
    intro h₀
    by_contra h₁
    rw [Decidable.not_and_iff_or_not] at h₁
    rw [<-ne_eq, <-ne_eq] at h₁
    cases h₁ with
    | inl h₁ =>
      -- If p ≠ 0, contradiction.
      replace h₀ : 1 / Real.sqrt 3 = -q / p := by
        calc
          1 / Real.sqrt 3 = p / Real.sqrt 3 / p := by rw [div_div, mul_comm, <-div_div, div_self]; norm_cast
          _ = (-q) / p := by congr; field_simp; linarith only [h₀]
      replace irrational_sqrt_three : Irrational (1 / Real.sqrt 3) := by
        apply Irrational.of_one_div
        simp
        exact irrational_sqrt_three
      rw [h₀] at irrational_sqrt_three
      absurd irrational_sqrt_three
      simp
      use -q / p
      simp
    | inr h₁ =>
      -- If q ≠ 0, contradiction.
      replace h₀ : Real.sqrt 3 = -p / q := by
        calc
          Real.sqrt 3 = q * Real.sqrt 3 / q := by rw [mul_div_cancel_left₀]; norm_cast
          _ = (-p) / q := by congr; linarith only [h₀]
      -- √3 is irrational.
      have h₁ : Irrational (Real.sqrt (3 : ℕ)) := by
        rw [irrational_sqrt_natCast_iff]
        native_decide -- Decide that 3 is not a square.
      rw [h₀] at irrational_sqrt_three
      absurd irrational_sqrt_three
      simp
      use -p / q
      simp
  -- We have 7 * a + 2 * b + 36 = 0 and 4 * a + b + 15 = 0.
  replace h : 7 * a + 2 * b + 36 = 0 ∧ 4 * a + b + 15 = 0 := by
    apply irrat_linear_combination
    simp [h]
  -- Solve the linear equation.
  linarith
