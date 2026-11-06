import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_88252 {P : ℕ → ℝ → ℝ}
  (hP0 : ∀ x, P 0 x = 2)
  (hP1 : ∀ x, P 1 x = x)
  (hP : ∀ n ≥ 2, ∀ x, P n x = x * P (n - 1) x - P (n - 2) x)
  (x : ℕ → ℝ)
  (hx : ∀ n, ∃ y, P n y = 0 ∧ |y| ≤ 2 ∧ ∀ z, P n z = 0 → |z| ≤ 2 → z ≤ y) :
  Tendsto (λ n => n ^ 2 * (4 - 2 * Real.pi + n ^ 2 * ∫ x in (x n)..2, P n x)) atTop
  (𝓝 (2 * Real.pi - 4 - Real.pi ^ 3 / 12)) := by

  have h2 := hx 0
  rcases h2 with ⟨y, h20, h21, h22⟩

  have h20' : P 0 y = 0 := by
    exact h20

  have h21' : P 0 y = 2 := hP0 y

  linarith