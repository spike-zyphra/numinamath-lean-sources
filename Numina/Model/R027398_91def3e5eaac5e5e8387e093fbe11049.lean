import Mathlib

theorem algebra_222961 {a b c : ℝ} (h₀ : ∃ r, b = a * r ∧ c = b * r)
    (h₁ : a + b + c = 7 / 3) (h₂ : a ^ 2 + b ^ 2 + c ^ 2 = 91 / 9) :
    (a = 3 ∧ b = -1 ∧ c = 1 / 3) ∨ (a = 1 / 3 ∧ b = -1 ∧ c = 3) := by
  rcases h₀ with ⟨r, h₃, h₄⟩
  have h₅ : c = a * r ^ 2 := by
    rw [h₄, h₃]
    all_goals ring
  rw [show b = a * r by linarith [h₃], show c = a * r ^ 2 by linarith [h₅]] at h₁
  rw [show b = a * r by linarith [h₃], show c = a * r ^ 2 by linarith [h₅]] at h₂
  have eq3 : a * r = -1 := by
    nlinarith [sq_nonneg (a * (r + 1 / a)), sq_nonneg (a - 3), sq_nonneg (a - 1 / 3)]
  have h6 : b = -1 := by
    nlinarith [h₃, eq3]
  have eq7 : a ≠ 0 := by
    by_contra h
    have ha0 : a = (0 : ℝ) := by linarith
    rw [ha0] at eq3
    nlinarith
  have eq8 : a ^ 2 - (10 / 3) * a + 1 = 0 := by
    have eq1' : a + a * r + a * r ^ 2 = 7 / 3 := by
      linarith
    have eq5' : a * r = -1 := by
      linarith [eq3]
    have : a * r ^ 2 = 1 / a := by
      have h8 : a * r = -1 := by
        nlinarith
      field_simp [eq7]
      <;> nlinarith
      <;> nlinarith
    nlinarith [eq1', eq5', this]
  have eq9 : (a - 3) * (a - 1 / 3) = 0 := by
    have h8 : 3 * a^2 - 10 * a + 3 = 0 := by
      linarith [eq8]
    nlinarith
  cases' (mul_eq_zero.1 eq9) with h10 h11
  · -- a = 3
    have ha3 : a = (3 : ℝ) := by linarith
    have h8 : r = (-1 / 3 : ℝ) := by
      have : a * r = -1 := by linarith [eq3]
      rw [ha3] at this
      field_simp at this ⊢
      <;> linarith
    have hc1 : c = (1 / 3 : ℝ) := by
      rw [h₅]
      rw [ha3]
      rw [h8]
      norm_num
      <;> nlinarith
    left
    exact ⟨by linarith, by linarith, by linarith⟩
  · -- a = 1/3
    have ha13 : a = (1 / 3 : ℝ) := by linarith
    have h9 : r = (-3 : ℝ) := by
      have : a * r = -1 := by linarith [eq3]
      rw [ha13] at this
      field_simp at this ⊢
      <;> linarith
    have hc3 : c = (3 : ℝ) := by
      rw [h₅]
      rw [ha13]
      rw [h9]
      norm_num
      <;> nlinarith
    right
    exact ⟨by linarith, by linarith, by linarith⟩