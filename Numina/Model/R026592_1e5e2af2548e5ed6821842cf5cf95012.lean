import Mathlib

theorem algebra_248434 (p : ℝ) (h : p > 0) (A B C : ℝ × ℝ)
    (hA : A = (-1, 1)) (hB : B = (1, -1)) (hAB : dist A B = 5 * Real.sqrt 2)
    (hC : C = (p / 2, 0)) (hC1 : dist C (p / 2, 0) = 4 / 3) :
    p = 3 ∨ p = 25 / 9 := by
  have h1 : dist C (p / 2, 0) = 0 := by
    rw [hC]
    simp [dist]
  have h2 : dist C (p / 2, 0) = 4 / 3 := hC1
  linarith