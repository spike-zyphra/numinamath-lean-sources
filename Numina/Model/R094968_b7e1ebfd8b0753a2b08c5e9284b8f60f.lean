import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_168450 :
  ¬ ∃ f : ℝ → ℝ, ∀ x, f (sin x) + f (cos x) = sin x := by
  intro h
  rcases h with ⟨f, hf⟩
  have h1 := hf (Real.pi / 2)
  have h2 := hf 0
  have h3 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
  have h4 : cos (Real.pi / 2) = 0 := by 
    rw [Real.cos_pi_div_two]
  have h5 : sin 0 = 0 := by simp
  have h6 : cos 0 = 1 := by simp
  rw [h3, h4] at h1
  rw [h5, h6] at h2
  linarith