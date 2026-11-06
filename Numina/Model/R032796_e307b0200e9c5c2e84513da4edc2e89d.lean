import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_230987 {f : ℝ → ℝ} (hf : f = λ x => log (abs (sin x))) :
    Even f ∧ Function.Periodic f Real.pi ∧ MonotoneOn f (Set.Ioo 0 (Real.pi/2)) := by
  constructor
  · -- Show that f is even
    use (λ x => (log (abs (sin x)) ) / 2)
    funext x
    simp [hf]
    all_goals ring
  constructor
  · -- Show that f is periodic with period π
    unfold Function.Periodic
    intro x
    rw [hf]
    have h1 : abs (sin (x + Real.pi)) = abs (sin x) := by
      have h2 : sin (x + Real.pi) = - sin x := Real.sin_add_pi x
      rw [h2]
      rw [abs_neg]
    simp [h1]
  · -- Show that f is monotone on (0, π/2)
    intro x hx y hy hxy
    rw [hf]
    simp at *
    have h11 : x > 0 := by
      have h11 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hx
      exact h11.1
    have h12 : x < Real.pi / 2 := by
      have h12 : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hx
      exact h12.2
    have h21 : y > 0 := by
      have h21 : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hy
      exact h21.1
    have h22 : y < Real.pi / 2 := by
      have h22 : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hy
      exact h22.2
    have h3 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith [show Real.pi/2 < Real.pi by linarith [Real.pi_pos]]
    have h4 : sin y > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith
      linarith [show Real.pi/2 < Real.pi by linarith [Real.pi_pos]]
    have h5 : abs (sin x) = sin x := by
      rw [abs_of_pos h3]
    have h6 : abs (sin y) = sin y := by
      rw [abs_of_pos h4]
    have h7 : sin x ≤ sin y := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      all_goals
      linarith
    have h8 : log (sin x) ≤ log (sin y) := by
      apply Real.log_le_log
      all_goals
      try linarith
    have h81 : log (abs (sin x)) ≤ log (abs (sin y)) := by
      rw [h5, h6]
      exact h8
    linarith