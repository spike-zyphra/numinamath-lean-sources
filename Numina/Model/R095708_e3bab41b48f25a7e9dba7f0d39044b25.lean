import Mathlib

open Real

theorem algebra_173210 {α β : ℝ} (hα : α ∈ Set.Icc 0 1) (hβ : β ∈ Set.Icc 0 1)
    (hαβ : α + β = 1) (h : (1 + 10 / 100) * α + (1 - 10 / 100) * β ≥
    (1 + 10 / 100) * (1 / 2) + (1 - 10 / 100) * (1 / 4) + (1 + 10 / 100) * (1 / 4)) :
    α ≥ 9 / 16 := by
  have hβ_eq : β = 1 - α := by linarith
  rw [hβ_eq] at h
  rcases hα with ⟨hα0, hα1⟩
  rcases hβ with ⟨hβ0, hβ1⟩
  linarith