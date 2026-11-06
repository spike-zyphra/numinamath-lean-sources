import Mathlib

theorem algebra_243411 (s r d : ℝ)
    (h₀ : 0 < s ∧ 0 < r ∧ 0 < d)
    (h₁ : 1 / s + 1 / r + 1 / d = 1 / 5)
    (h₂ : 1 / s + 1 / d = 1 / 7)
    (h₃ : 1 / r + 1 / d = 1 / 15) :
    1 / d = 1 / 105 := by
  rcases h₀ with ⟨hs, hr, hd⟩
  have eq1 : 1 / r = 2 / 35 := by 
    have eq2 : (1 / s + 1 / r + 1 / d) - (1 / s + 1 / d) = 1 / 5 - 1 / 7 := by
      linarith [h₁, h₂]
    have eq3 : (1 / s + 1 / r + 1 / d) - (1 / s + 1 / d) = 1 / r := by
      linarith
    linarith [eq3, eq2]
  have eq2 : 1 / d = 1 / 105 := by
    have eq3 : 1 / r + 1 / d = 1 / 15 := by linarith [h₃]
    rw [eq1] at eq3
    field_simp at eq3 ⊢
    <;> linarith
  linarith [eq2]