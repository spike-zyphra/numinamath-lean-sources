import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_231294 {f : ℝ → ℝ} (hf : f = λ x => log (abs (sin x))) :
    Even f ∧ Function.Periodic f π ∧ MonotoneOn f (Set.Ioo 0 (π/2)) := by 
  constructor
  · -- Show f is even
    rw [hf]
    use (fun x => (log (abs (sin x))) / 2)
    funext x
    simp [add_halves]
  constructor
  · -- Show f is periodic with period π
    rw [hf]
    unfold Function.Periodic
    intro x
    have h1 : abs (sin (x + Real.pi)) = abs (sin x) := by
      have h2 : sin (x + Real.pi) = - sin x := by 
        rw [Real.sin_add_pi]
      rw [h2]
      rw [abs_neg]
    have h3 : log (abs (sin (x + Real.pi))) = log (abs (sin x)) := by
      rw [h1]
    simpa using h3
  · -- Show f is monotone on Ioo 0 (π/2)
    rw [hf]
    intro x hx y hy h_le
    have h1 : 0 < x := hx.1
    have h2 : x < Real.pi / 2 := hx.2
    have h3 : 0 < y := hy.1
    have h4 : y < Real.pi / 2 := hy.2
    have hsin1 : sin x > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith [h1, Real.pi_pos]
      · linarith [h2, Real.pi_pos]
    have hsin2 : sin y > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      · linarith [h3, Real.pi_pos]
      · linarith [h4, Real.pi_pos]
    have h6 : sin x ≥ 0 := by
      linarith [hsin1]
    have h7 : sin y ≥ 0 := by
      linarith [hsin2]
    have h8 : abs (sin x) = sin x := by
      rw [abs_of_nonneg h6]
    have h9 : abs (sin y) = sin y := by
      rw [abs_of_nonneg h7]
    have h10 : sin x ≤ sin y := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      all_goals
      try linarith [h1, h2, h3, h4, h_le, Real.pi_pos]
    have h12 : log (abs (sin x)) ≤ log (abs (sin y)) := by
      rw [h8, h9]
      apply Real.log_le_log
      all_goals
      try linarith [hsin1, hsin2, h10]
    simpa using h12