import Mathlib

theorem algebra_130468 (a b c d : ℤ) (h₀ : a * b - 2 * c * d = 3) (h₁ : a * c + b * d = 1) :
    (a = 1 ∧ b = 3 ∧ c = 1 ∧ d = 0) ∨ (a = -1 ∧ b = -3 ∧ c = -1 ∧ d = 0) ∨
    (a = 3 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = -3 ∧ b = -1 ∧ c = 0 ∧ d = -1) := by
  have h2' : (a ^ 2 + 2 * d ^ 2) * (b ^ 2 + 2 * c ^ 2) = 11 := by
    nlinarith
  have h3 : (a ^ 2 + 2 * d ^ 2) * (b ^ 2 + 2 * c ^ 2) = 11 := h2'
  have h5 : (a ^ 2 + 2 * d ^ 2) ∣ 11 := by
    use (b ^ 2 + 2 * c ^ 2)
    all_goals linarith
  have h5' : (a ^ 2 + 2 * d ^ 2) ≥ 1 := by
    nlinarith [show 0 ≤ (a ^ 2 + 2 * d ^ 2 : ℤ) by nlinarith, sq_nonneg a, sq_nonneg d]
  have h5'' : (a ^ 2 + 2 * d ^ 2) = 1 ∨ (a ^ 2 + 2 * d ^ 2) = 11 := by
    have h5 : (a ^ 2 + 2 * d ^ 2) ∣ 11 := h5
    have h10 : (a ^ 2 + 2 * d ^ 2) ≤ 11 := by
      apply Int.le_of_dvd (by norm_num) h5
    have h11 : (a ^ 2 + 2 * d ^ 2) ≥ 1 := h5'
    interval_cases (a ^ 2 + 2 * d ^ 2) <;> omega
  cases h5'' with
  | inl h3_1 =>
    have h4 : a ^ 2 + 2 * d ^ 2 = 1 := by
      linarith
    have h5 : b ^ 2 + 2 * c ^ 2 = 11 := by
      nlinarith
    have h6 : d = 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (d), h4]
    have h7 : a ^ 2 = 1 := by
      nlinarith
    have h9 : a = 1 ∨ a = -1 := by
      have h10 : a ^ 2 = 1 := h7
      cases (sq_eq_one_iff.mp h10) with
      | inl h => tauto
      | inr h => tauto
    cases h9 with
    | inl h9_1 =>
      have h10 : b + c = 4 := by
        have h11 : a * c + b * d = 1 := h₁
        rw [h9_1, h6] at h11
        nlinarith 
      have h11 : b - c = 2 := by
        have h12 : a * b - 2 * c * d = 3 := h₀
        rw [h9_1, h6] at h12
        nlinarith 
      left
      exact ⟨h9_1, by nlinarith, by nlinarith, h6⟩
    | inr h9_1 =>
      have h10 : b + c = -4 := by
        have h11 : a * c + b * d = 1 := h₁
        rw [h9_1, h6] at h11
        nlinarith 
      have h11 : b - c = -2 := by
        have h12 : a * b - 2 * c * d = 3 := h₀
        rw [h9_1, h6] at h12
        nlinarith 
      right
      left
      exact ⟨h9_1, by nlinarith, by nlinarith, h6⟩
  | inr h3_1 =>
    have h4 : a ^ 2 + 2 * d ^ 2 = 11 := by
      linarith
    have h5 : b ^ 2 + 2 * c ^ 2 = 1 := by
      nlinarith
    have h6 : c = 0 := by
      nlinarith [sq_nonneg b, sq_nonneg c, h5]
    have h7 : b ^ 2 = 1 := by
      nlinarith
    have h9 : b = 1 ∨ b = -1 := by
      have h10 : b ^ 2 = 1 := h7
      cases (sq_eq_one_iff.mp h10) with
      | inl h => tauto
      | inr h => tauto
    cases h9 with
    | inl h9_1 =>
      have h10 : a + d = 4 := by
        have h11 : a * c + b * d = 1 := h₁
        rw [h6, h9_1] at h11
        nlinarith 
      have h11 : a - d = 2 := by 
        have h12 : a * b - 2 * c * d = 3 := h₀
        rw [h6, h9_1] at h12
        nlinarith 
      right
      right
      left 
      exact ⟨by nlinarith, h9_1, h6, by nlinarith⟩
    | inr h9_1 =>
      have h10 : a + d = -4 := by
        have h11 : a * c + b * d = 1 := h₁
        rw [h6, h9_1] at h11
        nlinarith 
      have h11 : a - d = -2 := by 
        have h12 : a * b - 2 * c * d = 3 := h₀
        rw [h6, h9_1] at h12
        nlinarith 
      right
      right
      right 
      exact ⟨by nlinarith, h9_1, h6, by nlinarith⟩