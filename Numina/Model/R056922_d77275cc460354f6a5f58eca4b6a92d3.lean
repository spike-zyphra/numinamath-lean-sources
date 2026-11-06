import Mathlib

theorem algebra_21895 (total_seniors : ℕ) (h₀ : total_seniors = 200)
    (history_takers : ℕ) (science_takers : ℕ) (h₁ : history_takers = 126) (h₂ : science_takers = 129) :
    history_takers + science_takers - total_seniors = 55 := by
  calc
    history_takers + science_takers - total_seniors = 126 + 129 - 200 := by rw [h₁, h₂, h₀]
    _ = 55 := by norm_num