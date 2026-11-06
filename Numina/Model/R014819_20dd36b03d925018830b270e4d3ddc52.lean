import Mathlib

theorem algebra_102300 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a^3 + b^3 + c^3 = 0) :
    a^19 + b^19 + c^19 = 0 := by
  have h2 : a * b * c = 0 := by
    have h_identity : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + b * c + c * a)) := by
      ring
    rw [h₀] at h_identity
    have h₃ : a^3 + b^3 + c^3 - 3 * a * b * c = 0 := by linarith
    have h₄ : a^3 + b^3 + c^3 = 3 * a * b * c := by linarith
    rw [h₁] at h₄
    linarith
  cases' (mul_eq_zero.mp h2) with h₅ h₆
  cases' (mul_eq_zero.mp h₅) with h₇ h₈
  · -- Case $a = 0$
    have ha₁ : a = 0 := h₇
    have hc₁ : c = -b := by
      linarith
    rw [ha₁, hc₁]
    ring_nf
  · -- Case $b = 0$
    have hb₁ : b = 0 := h₈
    have hc₂ : c = -a := by
      linarith
    rw [hb₁, hc₂]
    ring_nf
  · -- Case $c = 0$
    have hc₃ : c = 0 := h₆
    have hb₂ : b = -a := by
      linarith
    rw [hb₂, hc₃]
    ring_nf