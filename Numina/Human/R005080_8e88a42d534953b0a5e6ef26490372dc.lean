import Mathlib

open Real Set

/- Define

$$
f(x, y, z)=\frac{(x y+y z+z x)(x+y+z)}{(x+y)(x+z)(y+z)} .
$$

Determine the set of real numbers $r$ for which there exists a triplet $(x, y, z)$ of positive real numbers satisfying $f(x, y, z)=r$. -/
theorem algebra_605412 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : f = λ x y z => (x * y + y * z + z * x) * (x + y + z) / ((x + y) * (x + z) * (y + z))) :
    {r | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ f x y z = r} = {r | 1 < r ∧ r ≤ 9 / 8} := by
  ext r
  -- We can write f(x, y, z) as 1 + x * y * z / ((x + y) * (x + z) * (y + z))
  have hf' {x y z} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : f x y z = 1 + x * y * z / ((x + y) * (x + z) * (y + z)) := by
    field_simp [hf]
    ring
  simp only [mem_setOf_eq]
  constructor
  . -- We first prove that 1 < f(x, y, z) ≤ 9 / 8 for all x, y, z > 0
    rintro ⟨x, y, z, hx, hy, hz, rfl⟩
    rw [hf' hx hy hz]
    constructor
    . -- The first inequality is obvious
      simp only [lt_add_iff_pos_right]
      positivity
    . -- We cancel the denominator
      suffices x * y * z / ((x + y) * (x + z) * (y + z)) ≤ 1 / 8 by linarith only [this]
      rw [div_le_div_iff₀ (by positivity) (by simp)]
      -- It is equivalent to 0 ≤ x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2, which is true because x, y, z > 0
      suffices 0 ≤ x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 by linarith only [this]
      positivity
  . -- We need to show that for all r in (1, 9/8], there exists x, y, z > 0 such that f(x, y, z) = r
    rintro ⟨hr₁, hr₂⟩
    -- We simply take x = y = 1
    use 1, 1
    simp only [zero_lt_one, hf, mul_one, one_mul, true_and]
    -- We want to use the intermediate value theorem, so we need to show that the function (about z) is continuous on [0, 1]
    have hcont : ContinuousOn (fun (z : ℝ) => (1 + z + z) * (1 + 1 + z) / ((1 + 1) * (1 + z) * (1 + z))) (Icc 0 1) := by
      -- We can write the function as a quotient of two continuous functions
      apply ContinuousOn.div
      . -- The numerator is continuous
        apply Continuous.continuousOn
        clear * -
        continuity
      . -- The denominator is continuous
        apply Continuous.continuousOn
        clear * -
        continuity
      . -- The denominator is never 0 on [0, 1]
        simp only [mem_Icc, ne_eq, mul_eq_zero, add_self_eq_zero, one_ne_zero, false_or, or_self, and_imp]
        intro x hx₁ hx₂
        positivity
    -- Now we can use the intermediate value theorem
    -- So (1, 9/8] ⊆ f(1, 1, (0, 1])
    have H := intermediate_value_Ioc (by simp) hcont
    conv_lhs at H => norm_num
    -- We can find z in (0, 1) such that f(1, 1, z) = r
    rcases H ⟨hr₁, hr₂⟩ with ⟨z, hz₁, hz₂⟩
    exact ⟨z, hz₁.1, hz₂⟩
