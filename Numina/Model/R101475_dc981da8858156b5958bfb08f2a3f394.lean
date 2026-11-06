import Mathlib

theorem algebra_186411 {a b c : ℝ} (h₀ : a + b + c = 2) (h₁ : a^2 + b^2 + c^2 = 14 / 9)
    (h₂ : ∃ d, b = a + d ∧ c = b + d ∨ b = c + d ∧ a = b + d) :
    (a = 1 ∧ b = 2 / 3 ∧ c = 1 / 3) ∨ (a = 1 / 3 ∧ b = 2 / 3 ∧ c = 1) := by
  rcases h₂ with ⟨d, h₃⟩
  rcases h₃ with (h₃ | h₃)
  · -- Case where b = a + d ∧ c = b + d
    rcases h₃ with ⟨h₄, h₅⟩
    have h₆ : a = b - d := by linarith
    have h₇ : c = b + d := by linarith
    have h₈ : 3 * b = 2 := by
      have : a + b + c = 2 := h₀
      rw [show a = b - d by linarith, show c = b + d by linarith] at this
      linarith
    have h₉ : b = 2 / 3 := by linarith
    have h₁₀ : a^2 + b^2 + c^2 = 14 / 9 := h₁
    rw [show a = b - d by linarith, show c = b + d by linarith] at h₁₀
    rw [h₉] at h₁₀
    have h₁₁ : d ^ 2 = 1 / 9 := by
      nlinarith
    have h₁₂ : d = 1 / 3 ∨ d = -1 / 3 := by
      have : d ^ 2 - 1 / 9 = 0 := by linarith [h₁₁]
      have : (d - 1 / 3) * (d + 1 / 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h₁₄ h₁₅
      · -- Case where d - 1/3 = 0
        left
        linarith
      · -- Case where d + 1/3 = 0
        right
        linarith
    cases' h₁₂ with h₁₄ h₁₅
    · -- Case where d = 1/3
      have h₁₄₁ : d = 1 / 3 := h₁₄
      have ha₁ : a = 1 / 3 := by
        linarith [h₆, h₉, h₁₄₁]
      have hb₁ : b = 2 / 3 := h₉
      have hc₁ : c = 1 := by
        linarith [h₇, h₉, h₁₄₁]
      simp [ha₁, hb₁, hc₁]
    · -- Case where d = -1/3
      have h₁₅₁ : d = -1 / 3 := h₁₅
      have ha₂ : a = 1 := by
        linarith [h₆, h₉, h₁₅₁]
      have hb₂ : b = 2 / 3 := h₉
      have hc₂ : c = 1 / 3 := by
        linarith [h₇, h₉, h₁₅₁]
      simp [ha₂, hb₂, hc₂]
  · -- Case where b = c + d ∧ a = b + d
    rcases h₃ with ⟨h₆, h₇⟩
    have h₈ : a = b + d := by linarith
    have h₃₁ : c = b - d := by linarith
    have h₉ : 3 * b = 2 := by
      have : a + b + c = 2 := h₀
      rw [show a = b + d by linarith, show c = b - d by linarith] at this
      linarith
    have h₁₀ : b = 2 / 3 := by linarith
    have h₁₁ : a^2 + b^2 + c^2 = 14 / 9 := h₁
    rw [show a = b + d by linarith, show c = b - d by linarith] at h₁₁
    rw [h₁₀] at h₁₁
    have h₁₂ : d ^ 2 = 1 / 9 := by
      nlinarith
    have h₁₃ : d = 1 / 3 ∨ d = -1 / 3 := by
      have : d ^ 2 - 1 / 9 = 0 := by linarith [h₁₂]
      have : (d - 1 / 3) * (d + 1 / 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h₁₄ h₁₅
      · -- Case where d - 1/3 = 0
        left
        linarith
      · -- Case where d + 1/3 = 0
        right
        linarith
    cases' h₁₃ with h₁₄ h₁₅
    · -- Case where d = 1/3
      have h₁₄₁ : d = 1 / 3 := h₁₄
      have ha₁ : a = 1 := by
        linarith [h₈, h₁₀, h₁₄₁]
      have hb₁ : b = 2 / 3 := h₁₀
      have hc₁ : c = 1 / 3 := by
        linarith [h₃₁, h₁₀, h₁₄₁]
      simp [ha₁, hb₁, hc₁]
    · -- Case where d = -1/3
      have h₁₅₁ : d = -1 / 3 := h₁₅
      have ha₂ : a = 1 / 3 := by
        linarith [h₈, h₁₀, h₁₅₁]
      have hb₂ : b = 2 / 3 := h₁₀
      have hc₂ : c = 1 := by
        linarith [h₃₁, h₁₀, h₁₅₁]
      simp [ha₂, hb₂, hc₂]