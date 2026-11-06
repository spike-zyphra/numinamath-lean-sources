import Mathlib

theorem algebra_131110 {a b c d x : ℝ} (h₀ : a ≠ c) (h₁ : a + d = 2022) (h₂ : b + c = 2022)
    (h₃ : (x - a) * (x - b) = (x - c) * (x - d)) : x = 1011 := by 
  have h₄ : d = 2022 - a := by
    linarith 
  have h₅ : b = 2022 - c := by 
    linarith 
  rw [h₅, h₄] at h₃ 
  have h₆ : c - a ≠ 0 := by 
    intro h
    apply h₀
    linarith 
  have eq1 : (x - a) * (x - (2022 - c)) = (x - c) * (x - (2022 - a)) := h₃ 
  have eq2 : (c - a) * x = 1011 * (c - a) := by 
    nlinarith 
  have eq3 : x = 1011 := by
    apply (mul_left_inj' h₆).mp 
    linarith 
  exact eq3