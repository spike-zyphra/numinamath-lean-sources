import Mathlib

theorem inequalities_7905 {a b c : ℝ} (h₀ : a > b ∧ b > c) (h₁ : (a - b) * (b - c) * (c - a) = -1) :
    a - c ≥ 1.5 := by
  have h₂ : a > b := h₀.1
  have h₃ : b > c := h₀.2
  have h4 : a - b > 0 := sub_pos_of_lt h₂
  have h5 : b - c > 0 := sub_pos_of_lt h₃
  have h6 : a - c = (a - b) + (b - c) := by
    linarith
  have eq1 : (a - b) * (b - c) * (c - a) = - (a - b) * (b - c) * (a - c) := by
    have eq2 : c - a = - (a - c) := by
      linarith
    rw [eq2]
    <;> ring
  rw [eq1] at h₁
  have eq2 : (a - b) * (b - c) * (a - c) = 1 := by
    nlinarith
  nlinarith [sq_nonneg (a - b - (b - c)), sq_nonneg ((a - b) - 1.5 / 2), sq_nonneg ((b - c) - 1.5 / 2),
          sq_nonneg ((a - c) - 1.5), mul_pos h4 h5, mul_pos h4 (show 0 < a - c by linarith), 
          mul_pos h5 (show 0 < a - c by linarith)
        ]