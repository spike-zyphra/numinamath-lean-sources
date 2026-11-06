import Mathlib

theorem algebra_322555 (a b c : ℝ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c)
    (h₃ : a - b + c = 3) (h₄ : ∃ x, x^2 + a * x + 1 = 0 ∧ x^2 + b * x + c = 0)
    (h₅ : ∃ x, x^2 + x + a = 0 ∧ x^2 + c * x + b = 0) :
    a = -2 ∧ b = -3 ∧ c = 2 := by
  rcases h₄ with ⟨r, hr1, hr2⟩
  rcases h₅ with ⟨s, hs1, hs2⟩
  have eq1 : (b - a) * r + (c - 1) = 0 := by
    nlinarith
  have eq2 : (c - 1) * s + (b - a) = 0 := by
    nlinarith
  have h6 : r * s = 1 := by
    have h7 : b - a ≠ 0 := by
      intro h
      apply h₀
      linarith
    have eq6 : (b - a) * (1 - r * s) = 0 := by
      have eq7 : (c - 1) = - (b - a) * r := by linarith [eq1]
      rw [eq7] at eq2
      nlinarith [eq2]
    cases' (mul_eq_zero.mp eq6) with h5 h5
    · -- Case h5 : (b - a) = 0
      exfalso
      apply h₀
      linarith
    · -- Case h5 : (1 - r * s) = 0
      have : r * s = 1 := by
        nlinarith
      linarith
  have h7 : r^2 + a * r + 1 = 0 := by linarith
  have eq9 : 1 + r + a * r^2 = 0 := by
    have h8 : s^2 + s + a = 0 := by linarith
    have h9 : r ≠ 0 := by
      by_contra h
      have hr_eq0 : r = 0 := by linarith
      rw [hr_eq0] at h6
      nlinarith [sq_pos_of_ne_zero (show (1 : ℝ) ≠ 0 by norm_num)]
    have h10 : s = 1 / r := by
      have h9 : r ≠ 0 := h9
      field_simp at h6 ⊢
      <;> nlinarith [h6]
    rw [h10] at h8
    field_simp [h9] at h8 ⊢
    <;> nlinarith [sq_pos_of_ne_zero h9, sq_nonneg (r * r), sq_nonneg (r)]
  have h9 : r = 1 := by
    have h11 : r * (1 - r) = 0 := by
      nlinarith [sq_nonneg (r - 1), sq_nonneg (a * r - 1)]
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- r = 0
      have : r = 0 := by linarith
      exfalso
      have h5 : r ≠ 0 := by
        by_contra h
        rw [h] at h6
        nlinarith
      tauto
    · -- 1 - r = 0
      linarith
  have ha1 : a = -2 := by
    rw [show r = 1 by linarith [h9]] at hr1
    linarith
  have eq11 : b + c + 1 = 0 := by
    rw [show r = 1 by linarith [h9]] at eq1
    linarith
  have hc1 : c = 2 := by 
    nlinarith [eq11, h₃, ha1]
  have hb1 : b = -3 := by 
    nlinarith [eq11, ha1, hc1]
  exact ⟨ha1, hb1, hc1⟩