import Mathlib

theorem algebra_107394 (a : ℝ) (A B : Set ℝ)
    (hA : A = {x | x > 0 ∧ x < a}) (hB : B = {x | x < 0 ∧ x > a})
    (hAB : A ∩ B = {a}) :
    a ≤ -1 ∨ a ≥ 1 := by
  have h1 : a ∈ A ∩ B := by
    rw [hAB]
    simp
  have h2 : a ∈ A := by
    exact h1.1
  have h3 : a ∈ B := by
    exact h1.2
  rw [hA] at h2
  rw [hB] at h3
  have h4 : (a > 0 ∧ a < a) := by
    exact h2
  have h5 : (a < 0 ∧ a > a) := by
    exact h3
  have h6 : a < a := by
    linarith [h4.2]
  linarith