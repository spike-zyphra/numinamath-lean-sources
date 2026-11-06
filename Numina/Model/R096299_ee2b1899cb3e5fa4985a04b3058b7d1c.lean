import Mathlib

open Finset Real

theorem other_305274 {p : ℕ → ℝ} (hp : ∀ n, p n = (1 / 2) - (1 / 3) * (-2 / 3) ^ (n - 2)) :
    ∀ n, p n = (1 / 2) - (1 / 3) * (-2 / 3) ^ (n - 2) := by
  intro n
  exact hp n