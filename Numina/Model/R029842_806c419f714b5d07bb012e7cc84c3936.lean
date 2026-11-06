import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_3472 {f : ℝ → ℝ} (hf : f = λ x => exp (-x)) :
    IsGreatest {A | ∃ x, A = x * f x} (1 / exp 1) := by
  constructor
  · -- Show that 1 / exp 1 is in the set.
    use 1
    rw [hf]
    field_simp [exp_neg]
    all_goals norm_num
  · -- Show that for all A in the set, A ≤ 1 / exp 1
    intro A hA
    rcases hA with ⟨x, hx⟩
    rw [hx]
    rw [hf]
    have h1 : x * (exp (-x)) ≤ 1 / exp 1 := by
      have h2 : x ≤ exp (x - 1) := by
        have h3 : 1 + (x - 1) ≤ exp (x - 1) := by
          linarith [add_one_le_exp (x - 1)]
        have h4 : x ≤ exp (x - 1) := by
          linarith [h3]
        linarith
      have h5 : x * (exp (-x)) ≤ exp (-1) := by
        have h6 : exp (x - 1) * exp (-x) = exp (-1) := by
          have h7 : (x - 1 : ℝ) + (-x : ℝ) = (-1 : ℝ) := by ring
          calc
            exp (x - 1) * exp (-x) = exp ((x - 1 : ℝ) + (-x : ℝ)) := by rw [Real.exp_add]
            _ = exp (-1 : ℝ) := by rw [h7]
        have h7 : x * (exp (-x)) ≤ exp (x - 1) * exp (-x) := by
          have h8 : exp (-x) ≥ 0 := by positivity
          nlinarith [h2, h8]
        linarith [h7, h6]
      have h6 : exp (-1) = 1 / exp 1 := by
        field_simp [exp_neg]
      linarith [h5, h6]
    simpa using h1