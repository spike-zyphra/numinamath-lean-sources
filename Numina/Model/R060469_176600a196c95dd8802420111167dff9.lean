import Mathlib
open Real Set

theorem algebra_7692 :
  ¬ ∃ f : ℝ → ℝ, ∀ x, f (sin x) + f (cos x) = x := by
  intro h
  rcases h with ⟨f, hf⟩
  have h1 := hf 0
  have h1_eq : f (sin (0 : ℝ)) + f (cos (0 : ℝ)) = (0 : ℝ) := by
    simpa using h1
  have h1_zero : sin (0 : ℝ) = (0 : ℝ) := by
    simp
  have h1_one : cos (0 : ℝ) = (1 : ℝ) := by
    simp
  rw [h1_zero, h1_one] at h1_eq
  have h2 := hf (Real.pi / 2)
  have h2_eq : f (sin (Real.pi / 2 : ℝ)) + f (cos (Real.pi / 2 : ℝ)) = (Real.pi / 2 : ℝ) := by
    simpa using h2
  have h2_one : sin (Real.pi / 2 : ℝ) = (1 : ℝ) := by
    exact Real.sin_pi_div_two
  have h2_zero : cos (Real.pi / 2 : ℝ) = (0 : ℝ) := by
    exact Real.cos_pi_div_two
  rw [h2_one, h2_zero] at h2_eq
  all_goals
    linarith [Real.pi_pos]