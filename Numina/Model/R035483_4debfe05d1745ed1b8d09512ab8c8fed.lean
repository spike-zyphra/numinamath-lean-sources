import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9171 {f : ℝ → ℝ} (hf : f = λ x => exp x - x) : MonotoneOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  have h1 : 0 ≤ x := by
    simpa using hx
  have h2 : 0 ≤ y := by
    simpa using hy
  have h3 : x ≤ y := hxy
  have h4 : x ≥ 0 := h1
  have h5 : y ≥ 0 := h2
  have h11 : exp y - exp x ≥ y - x := by
    have h19 : x ≤ y := hxy
    have h20 : 0 ≤ x := h1
    have h21 : 0 ≤ y := h2
    have h12 : 0 ≤ y - x := by linarith
    have h13 : exp (y) = exp (x) * exp (y - x) := by 
      calc
        exp (y) = exp (x + (y - x)) := by ring_nf
        _ = exp (x) * exp (y - x) := by 
          rw [Real.exp_add]
    have h14 : exp y - exp x = exp x * (exp (y - x) - 1) := by
      rw [h13]
      all_goals 
        ring
    have h15 : exp x ≥ 1 := by
      have h16 : exp x ≥ exp (0 : ℝ) := by
        apply Real.exp_le_exp_of_le
        linarith
      have h17 : exp (0 : ℝ) = 1 := Real.exp_zero
      linarith
    have h18 : exp (y - x) ≥ 1 + (y - x) := by
      have h19 : y - x ≥ 0 := by linarith
      have h20 : exp (y - x) ≥ 1 + (y - x) := by
        linarith [Real.add_one_le_exp (y - x)]
      linarith
    have h19 : exp x * (exp (y - x) - 1) ≥ y - x := by
      have h19 : exp x * (exp (y - x) - 1) ≥ (1) * ( (y - x) ) := by
        have h19 : exp x ≥ 1 := h15
        have h20 : (exp (y - x) - 1) ≥ (y - x) := by
          linarith
        nlinarith
      linarith
    linarith [h14, h19]
  have h110 : (exp y - y) ≥ (exp x - x) := by
    linarith [h11]
  rw [hf]
  simp at *
  all_goals linarith