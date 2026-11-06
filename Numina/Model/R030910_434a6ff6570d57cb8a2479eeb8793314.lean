import Mathlib

open BigOperators Real Set

theorem algebra_217141 {f : ℝ → ℝ} (hf : f = λ x => abs (sin x)) :
    Even f ∧ (∃ c, Function.Periodic f c) := by
  constructor
  · -- Show that f is an even function
    rw [hf]
    use fun x => abs (Real.sin x) / 2
    funext x
    simp [abs_neg, Real.sin_neg]
    all_goals linarith
  · -- Show that f is periodic
    use 2 * Real.pi
    rw [hf]
    unfold Function.Periodic
    intro x
    have h2 : Real.sin (x + 2 * Real.pi) = Real.sin x := Real.sin_add_two_pi x
    simp [h2]