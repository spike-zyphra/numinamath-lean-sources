import Mathlib

/- Suppose $a, b$, and $c$ are distinct positive integers such that $\sqrt{a \sqrt{b \sqrt{c}}}$ is an integer. Compute the least possible value of $a+b+c$.-/
theorem number_theory_610583 :
    IsLeast {x | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∃ r : ℕ, r = Real.sqrt (a * Real.sqrt (b * Real.sqrt c)) ∧ x = a + b + c} 7 := by
  -- Simplify the goal into two parts.
  simp only [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Prove that 7 is possible.
    use 2, 4, 1
    norm_num
    use 2
    field_simp
    rw [<-Real.sqrt_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq, Real.sqrt_mul_self] <;> norm_num
  . -- Prove that 7 is the least possible value.
    intro x h
    obtain ⟨a, b, c, ha, hb, hc, h₀, h₁, h₂, r, h₃, h₄⟩ := h
    rw [h₄]
    clear h₄
    -- We have a√(b√c) = r².
    have h₄ := congr_arg (· ^ 2) h₃
    simp at h₄
    iterate 3 rw [<-Real.sqrt_mul (by simp)] at h₄
    rw [Real.sq_sqrt (by positivity)] at h₄
    -- We have b√c = (r² / a)².
    have h₅ : b * Real.sqrt c = (r ^ 2 / a) ^ 2 := by
      rw [h₄]
      field_simp
      rw [mul_pow]
      iterate 2 rw [Real.sq_sqrt (by positivity)]
    -- We have c = (r² / a)⁴ / b².
    have h₆ : c = ((r ^ 2 / a : ℝ) ^ 2 / b) ^ 2 := by
      rw [<-h₅]
      field_simp
    -- We show that c is a perfect square.
    have h₇ : ¬Irrational √c := by
      simp [Irrational]
      use (r ^ 2 / a : ℚ) ^ 2 / b
      rw [h₆, Real.sqrt_sq (by positivity)]
      push_cast
      rfl
    rw [irrational_sqrt_natCast_iff] at h₇
    -- Let c = c'².
    simp at h₇
    obtain ⟨c', hc'⟩ := h₇
    rw [<-pow_two] at hc'
    -- Show that bc' is a perfect square.
    have h₈ : ¬Irrational √(b * c' : ℕ) := by
      rw [hc'] at h₄
      push_cast at h₄
      rw [Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity)] at h₄
      simp [Irrational]
      use r ^ 2 / a
      field_simp [h₄]
    rw [irrational_sqrt_natCast_iff] at h₈
    simp at h₈
    obtain ⟨b', hb'⟩ := h₈
    rw [<-pow_two] at hb'
    -- Show that ab' is a perfect square.
    have h₉ : (a * b' : ℝ) = r ^ 2 := by
      rw [hc'] at h₄
      push_cast at h₄
      rify at hb'
      rw [Real.sqrt_sq (by positivity), hb', Real.sqrt_sq (by positivity)] at h₄
      tauto
    norm_cast at h₉
    -- First note that c' ≥ 1.
    have h₁₀ : 1 ≤ c' := by
      nlinarith
    -- Note that b' ≥ 2.
    have h₁₁ : 2 ≤ b' := by
      have h₁₁ : 1 ≤ b' := by
        nlinarith
      -- We cannot have b' = 1, otherwise b = c = 1, contradicting our assumption.
      have h₁₂ : b' ≠ 1 := by
        by_contra!
        simp [this] at hb'
        simp [hb'.2] at hc'
        simp [hb'.1, hc'] at h₁
      omega
    by_cases h₁₂ : c' = 1
    . -- If c' = 1, we have b ≥ 4.
      simp [h₁₂] at hc'
      have h₁₃ : 4 ≤ b := by
        nlinarith
      -- Assume 7 ≤ a + b + c is not satisfied, we derive that a = 1, b = 4 and c = 1, which does not work.
      by_contra!
      replace this : a = 1 := by
        omega
      simp [this, hc'] at h₂
    . -- If c' ≥ 2, we have c ≥ 4.
      replace h₁₂ : 2 ≤ c' := by
        omega
      have h₁₃ : 4 ≤ c := by
        nlinarith
      -- Assume 7 ≤ a + b + c is not satisfied, we derive that a = 1, b = 1 and c = 4, which does not work.
      by_contra!
      have h₁₄ : a = 1 := by
        omega
      have h₁₅ : b = 1 := by
        omega
      simp [h₁₄, h₁₅] at h₀
