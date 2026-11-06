import Mathlib

theorem algebra_16660 {a b c d : ℝ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : d ≠ 0) (h₄ : a / b = 4) (h₅ : b / c = 1 / 3) (h₆ : c / d = 6) :
    d / a = 1 / 8 := by
  have h7 : a = 4 * b := by
    field_simp [h₁] at h₄
    linarith
  have h8 : c = 3 * b := by
    field_simp [h₂] at h₅
    linarith
  have h9 : d = b / 2 := by
    field_simp [h₃] at h₆
    rw [show c = 3 * b by linarith [h8] ] at h₆
    linarith
  have h10 : d / a = 1 / 8 := by
    rw [show d = b / 2 by linarith [h9], show a = 4 * b by linarith [h7]]
    have hb : b ≠ 0 := h₁
    field_simp [hb, show (4 * b) ≠ 0 by
      intro h
      apply h₁
      linarith
    ]
    <;> ring_nf <;> field_simp [hb] <;> ring
  exact h10