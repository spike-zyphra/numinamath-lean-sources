import Mathlib

open Real Set

/-Let $x$ and $y$ be positive real numbers such that
\[\frac{1}{x + 2} + \frac{1}{y + 2} = \frac{1}{3}.\]Find the minimum value of $x + 2y.$-/
theorem algebra_16859 :
    IsLeast {z | ∃(x y : ℝ), 0 < x ∧ 0 < y ∧ 1 / (x + 2) + 1 / (y + 2) = 1 / 3 ∧ z = x + 2 * y} (3 + 6 * sqrt 2) := by
  have zero_lt_sqrt_2 : 0 < √2 := by norm_num
  constructor
  · -- Equality occurs when $(x + 2)^2 = 2(y + 2)^2,$ or $x + 2 = (y + 2) \sqrt{2}.$  Substituting into $\frac{1}{x + 2} + \frac{1}{y + 2} = \frac{1}{3},$ we get
    -- \[\frac{1}{(y + 2) \sqrt{2}} + \frac{1}{y + 2} = \frac{1}{3}.\]Solving, we find $y = \frac{2 + 3 \sqrt{2}}{2}.$  Then $x = 1 + 3 \sqrt{2}.$
    use (1 + 3 * √2)
    use (2 + 3 * √2) / 2
    ring_nf
    use (by linarith)
    use (by linarith)
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by positivity)]
    ring_nf
  · apply mem_lowerBounds.mpr
    simp
    intro z x hx y hy h hz
    rw [hz]
    have h : 1 / (x + 2) + 1 / (y + 2) = 1 / 3 := by
      simp
      exact h
    -- By the Cauchy-Schwarz inequality, \[((x + 2) + 2(y + 2)) \left( \frac{1}{x + 2} + \frac{1}{y + 2} \right) \ge (1 + \sqrt{2})^2.\]
    have ine₁: (x + 2 + 2 * (y + 2)) * (1 / (x + 2) + 1 / (y + 2)) ≥ (1 + sqrt 2) ^ 2 := by
      obtain ⟨S, hS⟩ := (by simp: ∃S : Finset ℕ, S = {0, 1})
      have : ∃a : ℕ → ℝ, a =
          fun n => match n with
          | 0 => √(x + 2)
          | 1 => √(2 * (y + 2))
          | _ => 0
        := by simp
      rcases this with ⟨a, ha⟩
      have : ∃b : ℕ → ℝ, b = fun n => match n with
          | 0 => √(1 / (x + 2))
          | 1 => √(1 / (y + 2))
          | _ => 0
        := by simp
      rcases this with ⟨b, hb⟩
      have : (∑ i ∈ S, a i * b i) = (1 + √2) := by
        simp [hS, ha, hb, add_assoc, ←one_div, mul_div]
        rw [div_self (sqrt_ne_zero'.mpr (by positivity)), ←mul_div]
        rw [div_self (sqrt_ne_zero'.mpr (by positivity)), mul_one]
      rw [this.symm]

      have : (x + 2 + 2 * (y + 2)) = (∑ i ∈ S, a i ^ 2) := by
        simp [hS, ha, hb, mul_pow]
        repeat rw [Real.sq_sqrt (by linarith)]
      rw [this]
      have : (1 / (x + 2) + 1 / (y + 2)) = (∑ i ∈ S, b i ^ 2) := by
        simp [hS, ha, hb]
        repeat rw [Real.sq_sqrt (by linarith)]
      rw [this]
      apply Finset.sum_mul_sq_le_sq_mul_sq

    -- Then \[x + 2 + 2y + 4 \ge 3 (1 + \sqrt{2})^2 = 9 + 6 \sqrt{2},\]
    have ine₂: x + 2 + 2 * y + 4 ≥ 9 + 6 * √2 := by
      simp
      have : 9 + 6 * √2 = 3 * (1 + √2) ^ 2 := by
        rw [add_pow_two, Real.sq_sqrt (by positivity)]
        ring_nf
      rw [this]
      have : x + 2 + 2 * y + 4 = (x + 2 + 2 * (y + 2)) := by linarith
      rw [this, mul_comm]
      apply (le_mul_inv_iff₀ (by positivity)).mp
      rw [←one_div, h.symm]
      exact ine₁
    -- so $x + 2y \ge 3 + 6 \sqrt{2}.$
    linarith
