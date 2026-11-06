import Mathlib

/- Find the positive real number(s) $x$ such that $\frac{1}{2}\left(3 x^{2}-1\right)=\left(x^{2}-50 x-10\right)\left(x^{2}+25 x+5\right)$.-/
theorem algebra_608243 :
    {x : ℝ | 0 < x ∧ 1 / 2 * (3 * x ^ 2 - 1) = (x ^ 2 - 50 * x - 10) * (x ^ 2 + 25 * x + 5)} = {25 + 2 * Real.sqrt 159} := by
  -- Simplify the goal into two parts.
  ext x
  simp [-one_div]
  apply Iff.intro
  . -- Show that the equation implies the solution.
    rintro ⟨hx, h₀⟩
    -- Let a = x² - 50x - 10 and b = x² + 25x + 5.
    let a := x ^ 2 - 50 * x - 10
    let b := x ^ 2 + 25 * x + 5
    -- Change the equation to (a + 2b - 1) / 2 = ab.
    rw [show x ^ 2 - 50 * x - 10 = a by rfl, show x ^ 2 + 25 * x + 5 = b by rfl, show 3 * x ^ 2 - 1 = a + 2 * b - 1 by ring] at h₀
    -- Change the equation to (a - 1)(2b - 1) = 0.
    replace h₀ : (a - 1) * (2 * b - 1) = 0 := by
      ring_nf at h₀ ⊢
      linarith only [h₀]
    simp at h₀
    -- Now a = 1 or 2b - 1 = 0.
    cases h₀ with
    | inl h₀ =>
      -- Suppose a = 1.
      simp [a] at h₀
      -- Rewrite the equation and solve it.
      replace h₀ : (x - 25) ^ 2 = (2 * Real.sqrt 159) ^ 2 := by
        rw [mul_pow]
        field_simp
        linarith only [h₀]
      rw [sq_eq_sq_iff_eq_or_eq_neg] at h₀
      -- There are two solutions upon considerations.
      cases h₀ with
      | inl h₀ =>
        -- We have solution x = 25 + 2√159 > 0.
        linarith only [h₀]
      | inr h₀ =>
        -- We have solution x = 25 - 2√159, but it is nonpositive, a contradiction.
        linarith only [h₀, hx, show 25 / 2 < Real.sqrt 159 by rw [Real.lt_sqrt]; norm_num; norm_num]
    | inr h₀ =>
      -- Suppose b = 1/2.
      simp [b] at h₀
      -- Rewrite the equation and solve it.
      replace h₀ : (2 * x + 25) ^ 2 = 607 := by
        linarith only [h₀]
      -- It has no positive solution becuase if x > 0, left-hand side is greater than 607.
      absurd h₀
      rw [<-ne_eq]
      apply LT.lt.ne'
      calc
        (607 : ℝ) < 25 ^ 2 := by norm_num
        _ < (2 * x + 25) ^ 2 := by
          rw [sq_lt_sq₀]
          all_goals
            linarith
  . -- Show that x = 25 + 2√159 is indeed a solution.
    intro hx
    rw [hx]
    refine ⟨by positivity, ?_⟩
    ring_nf
    rw [show Real.sqrt 159 ^ 3 = Real.sqrt 159 * Real.sqrt 159 ^ 2 by ring, show Real.sqrt 159 ^ 4 = Real.sqrt 159 ^ 2 * Real.sqrt 159 ^ 2 by ring]
    field_simp
    ring
    