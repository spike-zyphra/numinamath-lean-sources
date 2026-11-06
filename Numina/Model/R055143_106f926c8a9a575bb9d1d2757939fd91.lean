import Mathlib

theorem algebra_321549 {a b c d : ℝ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : d ≠ 0) (h₄ : ∃ r, b = a * r ∧ c = b * r ∧ d = c * r) :
    a * d = b * c := by 
  rcases h₄ with ⟨r, hb, hc, hd⟩
  have hc2 : c = a * r^2 := by
    rw [hb] at hc 
    linarith
  have hd2 : d = a * r^3 := by 
    rw [hc2] at hd 
    linarith
  rw [hd2, hb, hc2]
  <;> ring