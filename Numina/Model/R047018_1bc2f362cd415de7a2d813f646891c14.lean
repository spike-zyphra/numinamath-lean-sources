import Mathlib

theorem inequalities_135093 {a a' b b' c c' : ℝ} (h₀ : a * a' > 0) (h₁ : a * c ≥ b^2) (h₂ : a' * c' ≥ b'^2) :
    (a + a') * (c + c') ≥ (b + b')^2 := by
  have h3 : a * a' > 0 := h₀
  have h4 : a > 0 ∧ a' > 0 ∨ a < 0 ∧ a' < 0 := by
    apply Or.elim (mul_pos_iff.mp h₀)
    · -- Case where a > 0 and a' > 0
      intro h
      tauto
    · -- Case where a < 0 and a' < 0
      intro h
      tauto
  cases h4 with
  | inl ha_pos =>
    have h5 : a > 0 := ha_pos.1
    have h6 : a' > 0 := ha_pos.2
    have h7 : a' * (a * c) ≥ a' * (b ^ 2) := by
      have h7 : a * c ≥ b ^ 2 := h₁
      have h8 : a' ≥ 0 := by linarith
      nlinarith
    have h9 : a * (a' * c') ≥ a * (b' ^ 2) := by
      have h9 : a' * c' ≥ b' ^ 2 := h₂
      have h10 : a ≥ 0 := by linarith
      nlinarith
    nlinarith [sq_nonneg (a * b' - a' * b), sq_nonneg (b - b'), sq_nonneg (a * c' - a' * c)]
  | inr ha_neg =>
    have h5 : a < 0 := ha_neg.1
    have h6 : a' < 0 := ha_neg.2
    have h7 : a' * (a * c) ≤ a' * (b ^ 2) := by
      have h7 : a * c ≥ b ^ 2 := h₁
      have h8 : a' < 0 := by linarith
      nlinarith
    have h9 : a * (a' * c') ≤ a * (b' ^ 2) := by
      have h9 : a' * c' ≥ b' ^ 2 := h₂
      have h10 : a < 0 := by linarith
      nlinarith
    nlinarith [sq_nonneg (a * b' - a' * b), sq_nonneg (b - b'), sq_nonneg (a * c' - a' * c)]