import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a b c=1$. Prove that:

$\left(a^{5}+a^{4}+a^{3}+a^{2}+a+1\right)\left(b^{5}+b^{4}+b^{3}+b^{2}+b+1\right)\left(c^{5}+c^{4}+c^{3}+c^{2}+c+1\right) \geq 8\left(a^{2}+a+1\right)\left(b^{2}+b+1\right)\left(c^{2}+c+1\right)$. -/
theorem inequalities_605765 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) :
    (a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1) * (b ^ 5 + b ^ 4 + b ^ 3 + b ^ 2 + b + 1) * (c ^ 5 + c ^ 4 + c ^ 3 + c ^ 2 + c + 1) ≥ 8 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by
  -- We prove the simple lemma tha x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = (x ^ 3 + 1) (x ^ 2 + x + 1).
  have h₀ (x : ℝ) : x ^ 5 + x ^ 4 + x ^ 3 + x ^ 2 + x + 1 = (x ^ 3 + 1) * (x ^ 2 + x + 1) := by
    ring
  -- We prove the simple lemma that x ^ 3 + 1 ≥ 2 √(x ^ 3) for all x > 0.
  have h₁ (x : ℝ) (hx : 0 < x) : 2 * Real.sqrt (x ^ 3) ≤ x ^ 3 + 1 := by
    rw [<-sq_le_sq₀, mul_pow, Real.sq_sqrt]
    linarith only [sq_nonneg (x ^ 3 - 1)]
    all_goals
      positivity
  -- Apply lemma h₀.
  rw [h₀ a, h₀ b, h₀ c]
  calc
    (a ^ 3 + 1) * (a ^ 2 + a + 1) * ((b ^ 3 + 1) * (b ^ 2 + b + 1)) * ((c ^ 3 + 1) * (c ^ 2 + c + 1))
    _ = (a ^ 3 + 1) * (b ^ 3 + 1) * (c ^ 3 + 1) * ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) := by ac_rfl
    _ ≥ (2 * Real.sqrt (a ^ 3)) * (2 * Real.sqrt (b ^ 3)) * (2 * Real.sqrt (c ^ 3)) * ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) := by
      -- Apply lemma h₁.
      rw [ge_iff_le, mul_le_mul_right (by positivity)]
      apply mul_le_mul
      apply mul_le_mul
      apply h₁ a ha
      apply h₁ b hb
      positivity
      positivity
      apply h₁ c hc
      positivity
      positivity
    _ = 2 * 2 * 2 * Real.sqrt ((a * b * c) ^ 3) * ((a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1)) := by
      -- Simple arithmetic manipulation.
      rw [mul_pow, mul_pow, Real.sqrt_mul, Real.sqrt_mul]
      congrm ?_ * ?_
      . ac_rfl
      . rfl
      all_goals
        positivity
    _ = 8 * (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by
      -- Apply habc to replace a * b * c by 1.
      simp [habc]
      ring
      