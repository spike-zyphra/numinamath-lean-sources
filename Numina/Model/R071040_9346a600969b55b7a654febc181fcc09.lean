import Mathlib

theorem algebra_94190 {a b c d : ℝ} (h₀ : b ≠ -c) (h₁ : d ≠ -a) (h₂ : (a + b) / (b + c) = (c + d) / (d + a)) :
    a = c ∨ a + b + c + d = 0 := by
  have h3 : b + c ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h4 : d + a ≠ 0 := by
    intro h
    apply h₁
    linarith
  have h5 : (a + b) * (d + a) = (c + d) * (b + c) := by
    field_simp [h3, h4] at h₂ ⊢
    linarith
  have h7 : (a - c) * (a + b + c + d) = 0 := by
    have eq1 : (a + b) * (d + a) - (c + d) * (b + c) = 0 := by
      linarith [h5]
    have h8 : (a + b) * (d + a) - (c + d) * (b + c) = (a - c) * (a + b + c + d) := by
      ring
    rw [h8] at eq1
    linarith
  cases' (mul_eq_zero.1 h7) with h9 h10
  · -- Case where a - c = 0, so a = c
    left
    linarith
  · -- Case where a + b + c + d = 0
    right
    linarith