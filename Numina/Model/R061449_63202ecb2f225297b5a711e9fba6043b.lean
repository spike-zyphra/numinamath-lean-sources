import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_312186 (a b : ℝ) (D : Set (ℝ × ℝ))
  (hD : D = {(x, y) | x + y ≤ 1 ∧ 2 * x - y ≥ -1 ∧ x - 2 * y ≤ 1})
  (hAB : ∀ x y : ℝ, (x, y) ∈ D → (x * a + y * b) ≤ 1) :
  a + b ≤ 2 := by

  have h1 := hAB 1 0 (by
    rw [hD]
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  )

  have h2 := hAB 0 1 (by
    rw [hD]
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  )

  have h3 := hAB (1 / 2) (1 / 2) (by
    rw [hD]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  )

  linarith