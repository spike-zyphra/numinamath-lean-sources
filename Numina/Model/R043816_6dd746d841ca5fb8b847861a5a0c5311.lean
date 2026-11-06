import Mathlib

theorem algebra_52009 (Hₘ Hₚ Kₘ Kₚ : ℝ)
    (h₀ : 0 < Hₘ ∧ 0 < Hₚ ∧ 0 < Kₘ ∧ 0 < Kₚ)
    (h₁ : Hₘ + Hₚ = 9)
    (h₂ : Hₘ + Kₚ = 8)
    (h₃ : Kₘ + Hₚ = 7)
    (h₄ : Kₘ + Kₚ = 6)
    (h₅ : Kₚ = 2 * Kₘ) :
    ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m.Coprime n ∧ 
      1 / (1 / Hₘ + 1 / Kₘ) + 1 / (1 / Hₚ + 1 / Kₚ) = m / n ∧ 
      m + n = 41 := by

  have h₆ : Kₘ = 2 := by
    have eq1 : Kₘ + Kₚ = 6 := by linarith
    rw [show Kₚ = 2 * Kₘ by linarith [h₅]] at eq1
    linarith
  have h₇ : Kₚ = 4 := by
    linarith [h₆, h₅]
  have h₈ : Hₘ = 4 := by
    linarith [h₇, h₂]
  have h₉ : Hₚ = 5 := by
    linarith [h₆, h₃]

  use 32, 9
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num [Nat.Coprime]
  constructor
  · -- Verify the equation
    rw [show Hₘ = 4 by linarith [h₈], show Kₘ = 2 by linarith [h₆], 
        show Hₚ = 5 by linarith [h₉], show Kₚ = 4 by linarith [h₇]]
    norm_num
  · -- Verify m + n = 41
    norm_num