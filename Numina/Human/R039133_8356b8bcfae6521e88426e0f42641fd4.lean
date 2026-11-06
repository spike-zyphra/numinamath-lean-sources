import Mathlib

theorem algebra_605274 (a b c : ℝ) (h₁ : a * b + b * c + c * a = 1) (h₂ : a ^ 2 * b + c = b ^ 2 * c + a) (h₃ : b ^ 2 * c + a = c ^ 2 * a + b) :
  (a = 0 ∧ b = 1 ∧ c = 1) ∨ (a = 0 ∧ b = -1 ∧ c = -1) ∨
  (a = 1 ∧ b = 0 ∧ c = 1) ∨ (a = -1 ∧ b = 0 ∧ c = -1) ∨
  (a = 1 ∧ b = 1 ∧ c = 0) ∨ (a = -1 ∧ b = -1 ∧ c = 0) ∨
  (a = 1 / Real.sqrt 3 ∧ b = 1 / Real.sqrt 3 ∧ c = 1 / Real.sqrt 3) ∨
  (a = -1 / Real.sqrt 3 ∧ b = -1 / Real.sqrt 3 ∧ c = -1 / Real.sqrt 3) := by
  -- Subtle lemma that 0 ≠ √3 and 0 ≠ -1/√3.
  have : ¬0 = Real.sqrt 3 ∧ ¬0 = -1 / Real.sqrt 3 := by
    rw [<-sq_eq_sq₀, Real.sq_sqrt, eq_div_iff]
    all_goals
      norm_num
  -- Use case analysis to handle all easy cases with some zero in a, b, c.
  by_cases h₄ : a = 0 <;>
    by_cases h₅ : b = 0 <;>
      by_cases h₆ : c = 0 <;>
        simp_all [this]
  . -- Case a = 0 and b, c ≠ 0.
    cases h₂ with
    | inl h₂ =>
      rw [h₂] at h₁
      left
      refine ⟨h₂, by linarith only [h₁]⟩
    | inr h₂ =>
      rw [h₂] at h₁
      right
      refine ⟨h₂, by linarith only [h₁]⟩
  . -- Now we may assume that a, b, c are all non-zero.
    -- Multiply h₁ by a.
    have h₇ : a * (a * b + b * c + c * a) = a * 1 := by
      rw [mul_right_inj' (by exact h₄)]
      exact h₁
    -- Multiply h₁ by b.
    have h₈ : b * (a * b + b * c + c * a) = b * 1 := by
      rw [mul_right_inj' (by exact h₅)]
      exact h₁
    -- Multiply h₁ by c.
    have h₉ : c * (a * b + b * c + c * a) = c * 1 := by
      rw [mul_right_inj' (by exact h₆)]
      exact h₁
    -- Use h₇ and h₂, h₃ to prove a² + ab + b² = 1.
    have h₁₀ : c * (a ^ 2 + a * b + b ^ 2) = c * 1 := by
      linarith only [h₇, h₂, h₃]
    rw [mul_right_inj' (by exact h₆)] at h₁₀
    -- Use h₉ and h₂ to prove c² + ca + a² = 1.
    have h₁₁ : b * (c ^ 2 + c * a + a ^ 2) = b * 1 := by
      linarith only [h₉, h₂]
    rw [mul_right_inj' (by exact h₅)] at h₁₁
    -- Use h₈ and h₃ to prove b² + bc + c² = 1.
    have h₁₂ : a * (b ^ 2 + b * c + c ^ 2) = a * 1 := by
      linarith only [h₈, h₃]
    rw [mul_right_inj' (by exact h₄)] at h₁₂
    -- Now, combining equalities above, we have c² = ab, b² = ac and a² = bc.
    have h₁₃ : c ^ 2 = a * b := by
      linarith
    have h₁₄ : b ^ 2 = a * c := by
      linarith
    have h₁₅ : a ^ 2 = b * c := by
      linarith
    -- Now we have a = b = c.
    have h₁₆ : a = b := by
      nlinarith
    have h₁₇ : b = c := by
      nlinarith
    -- Rewrite a = b = c into h₁.
    rw [h₁₆, h₁₇] at h₁
    replace h₁ : c ^ 2 = 1 / 3 := by
      linarith only [h₁]
    -- Separate the cases c < 0 and c ≥ 0.
    cases le_or_lt 0 c with
    | -- Case c ≥ 0.
      inl h₁₈ =>
      rw [<-Real.sqrt_inj (by positivity) (by norm_num), Real.sqrt_sq h₁₈, Real.sqrt_div (by norm_num)] at h₁
      ring_nf at h₁
      simp at h₁
      rw [h₁] at h₁₇
      rw [h₁₇] at h₁₆
      tauto
    | -- Case c < 0.
      inr h₁₈ =>
      rw [<-neg_sq, <-Real.sqrt_inj (by positivity) (by norm_num), Real.sqrt_sq (by linarith only [h₁₈]), Real.sqrt_div (by norm_num), show Real.sqrt 1 = 1 by norm_num] at h₁
      rw [neg_eq_iff_eq_neg, <-neg_div] at h₁
      rw [h₁] at h₁₇
      rw [h₁₇] at h₁₆
      tauto
