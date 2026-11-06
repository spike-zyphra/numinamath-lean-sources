import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_305325 {f : ℝ → ℝ} (hf : f = λ x => -log (abs (sin x))) :
    (∀ x, f (x + π) = f x) ∧ MonotoneOn (-f) (Set.Ioo 0 (π/2)) ∧ Even f := by
  constructor
  · -- Proof that f(x + π) = f(x) for all x
    intro x
    have h1 : sin (x + π) = - sin x := by
      rw [sin_add_pi]
    have h2 : abs (sin (x + π)) = abs (sin x) := by
      rw [h1]
      rw [abs_neg]
    calc
      f (x + π) = -log (abs (sin (x + π))) := by rw [hf]
      _ = -log (abs (sin x)) := by rw [h2]
      _ = f x := by rw [hf]
  constructor
  · -- Proof that -f is monotone on (0, π/2)
    intro x hx y hy hxy
    have hx1 : 0 < x := by
      have h1 : x ∈ Set.Ioo (0 : ℝ) (π / 2) := hx
      exact h1.1
    have hx2 : x < π / 2 := by
      have h1 : x ∈ Set.Ioo (0 : ℝ) (π / 2) := hx
      exact h1.2
    have hy1 : 0 < y := by
      have h2 : y ∈ Set.Ioo (0 : ℝ) (π / 2) := hy
      exact h2.1
    have hy2 : y < π / 2 := by
      have h2 : y ∈ Set.Ioo (0 : ℝ) (π / 2) := hy
      exact h2.2
    have h3 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos, show x < π by linarith [show x < π / 2 by linarith [Real.pi_pos], Real.pi_gt_three]]
    have h4 : sin y > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos, show y < π by linarith [show y < π / 2 by linarith [Real.pi_pos], Real.pi_gt_three]]
    have h5 : sin x ≤ sin y := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      all_goals
      linarith [Real.pi_pos]
    -- Since sin x ≤ sin y, and logarithm is increasing, we have log(sin x) ≤ log(sin y)
    have h6 : abs (sin x) = sin x := by
      rw [abs_of_pos h3]
    have h7 : abs (sin y) = sin y := by
      rw [abs_of_pos h4]
    have h8 : log (abs (sin x)) ≤ log (abs (sin y)) := by
      rw [h6, h7]
      apply Real.log_le_log
      all_goals
      linarith [h3, h4]
    -- Therefore, -log(sin x) ≥ -log(sin y), i.e., -f x ≤ -f y
    simp [hf] at *
    linarith [h8]
  · -- Proof that f is an even function
    use (fun x => (-log (abs (sin x))) / 2)
    funext x
    simp [hf]
    all_goals
      ring