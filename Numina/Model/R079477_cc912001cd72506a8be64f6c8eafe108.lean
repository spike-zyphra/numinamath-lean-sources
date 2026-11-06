import Mathlib

open Real

theorem algebra_12489 {f : ℝ → ℝ} (hf : ∀ x, f x = ⌊x⌋ + 1 / 2) :
    ¬(∀ x, f x = f (-x)) ∧ ¬(∀ x, f x = -f (-x)) := by 
  constructor
  · -- Assume f is even
    intro heven
    have h1 := heven 0.5
    rw [hf, hf] at h1
    norm_num at h1
    all_goals omega
  · -- Assume f is odd 
    intro hodd
    have h2 := hodd 1
    rw [hf, hf] at h2
    norm_num at h2
    all_goals omega