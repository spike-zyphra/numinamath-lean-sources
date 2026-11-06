import Mathlib

theorem algebra_142893 (a b c : ℝ) (h₀ : a + b + c = 10) (h₁ : a = 10 * 0.1) (h₂ : b = c / 2) :
    a = 1 ∧ b = 3 ∧ c = 6 := by
  have ha1 : a = 1 := by
    rw [h₁]
    norm_num
  have hc : c = 6 := by
    have eq1 : a + b + c = 10 := h₀
    rw [show a = 1 by exact ha1] at eq1 -- substitute a = 1
    rw [show b = c / 2 by linarith [h₂]] at eq1 -- substitute b = c / 2
    linarith -- solve 1 + c / 2 + c = 10 to get c = 6
  have hb : b = 3 := by
    rw [show c = 6 by exact hc] at h₂ -- substitute c = 6 in b = c / 2
    linarith -- solve b = 6 / 2, so b = 3
  exact ⟨ha1, hb, hc⟩