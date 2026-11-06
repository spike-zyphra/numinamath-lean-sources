import Mathlib

/- For any positive real numbers $a$ and $b$, define $a \circ b=a+b+2 \sqrt{a b}$. Find all positive real numbers $x$ such that $x^{2} \circ 9 x=121$.-/
theorem algebra_608834 (δ : ℝ × ℝ → ℝ) (hδ : ∀ a b, 0 < a → 0 < b → δ (a, b) = a + b + 2 * Real.sqrt (a * b)) :
    {x : ℝ | 0 < x ∧ δ (x ^ 2, 9 * x) = 121} = {(31 - 3 * Real.sqrt 53) / 2} := by
  -- Change the form of δ to δ(a, b) = (√a + √b)².
  replace hδ (a b : ℝ) : 0 < a → 0 < b → δ (a, b) = (Real.sqrt a + Real.sqrt b) ^ 2 := by
    intro ha hb
    rw [hδ _ _ ha hb]
    ring_nf
    field_simp
    ring_nf
  -- Simplify the goal into two parts.
  ext x
  simp
  apply Iff.intro
  . -- First show that δ(x², 9x) implies the solution.
    rintro ⟨h₀, h₁⟩
    -- We have x + 3√x = 11.
    rw [hδ, show (121 : ℝ) = 11 ^ 2 by norm_num, sq_eq_sq₀, Real.sqrt_sq, Real.sqrt_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq] at h₁
    -- Rewrite the equation to get (2√x + 3)² = 53.
    replace h₁ : (2 * Real.sqrt x + 3) ^ 2 = Real.sqrt 53 ^ 2 := by
      ring_nf
      field_simp
      linarith only [h₁]
    -- Since 0 ≤ 2√x + 3, we only have one solution.
    rw [sq_eq_sq₀] at h₁
    rw [show x = Real.sqrt x ^ 2 by rw [Real.sq_sqrt]; positivity, show Real.sqrt x = (Real.sqrt 53 - 3) / 2 by linarith only [h₁]]
    ring_nf
    field_simp
    ring_nf
    all_goals
      positivity
  . -- Show that (31 - 3√53) / 2 satisfies the equation.
    intro h₀
    -- Justify that (31 - 3√53) / 2 > 0.
    have hx : x > 0 := by
      simp [h₀]
      rw [mul_comm, <-lt_div_iff₀, Real.sqrt_lt]
      all_goals
        norm_num
    -- It suffices to show that Real.sqrt x = (Real.sqrt 53 - 3) / 2.
    have h₁ : Real.sqrt x = (Real.sqrt 53 - 3) / 2 := by
      suffices x = ((Real.sqrt 53 - 3) / 2) ^ 2 by
        rw [<-Real.sq_sqrt (le_of_lt hx)] at this
        rw [sq_eq_sq₀ (by positivity)] at this
        exact this
        rw [le_div_iff₀]
        simp
        rw [Real.le_sqrt]
        all_goals
          norm_num
      ring_nf
      field_simp
      linarith only [h₀]
    refine ⟨hx, ?_⟩
    -- Verify that δ(x², 9x) = 121.
    rw [hδ _ _ (by positivity) (by positivity), show (121 : ℝ) = 11 ^ 2 by norm_num, sq_eq_sq₀ (by positivity), Real.sqrt_mul, h₁, Real.sqrt_sq (by positivity), h₀, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq]
    ring_nf
    all_goals
      norm_num

