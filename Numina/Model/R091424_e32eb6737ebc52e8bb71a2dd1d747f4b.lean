import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_296401 {f g : ℝ → ℝ}
  (hf : f = λ x => x + x^2 - x^5) (hg : g = λ x => sin x - cos x) :
  ¬ (∀ x, f (-x) = f x) ∧ ¬ (∀ x, g (-x) = g x) ∧ ¬ (∀ x, f (-x) = -f x) ∧ ¬ (∀ x, g (-x) = -g x) := by
  constructor
  · -- f is not even
    intro h
    specialize h 2
    rw [hf] at h
    norm_num at h
  constructor
  · -- g is not even
    intro h
    specialize h (Real.pi / 2)
    rw [hg] at h
    have h1 : sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    have h2 : cos (Real.pi / 2) = 0 := by
      rw [Real.cos_pi_div_two]
    have h3 : sin (- (Real.pi / 2)) = -1 := by
      rw [show - (Real.pi / 2) = - (Real.pi / 2) by ring]
      have : sin (- (Real.pi / 2)) = - sin (Real.pi / 2) := by rw [sin_neg]
      rw [this, h1]
      all_goals norm_num
    have h4 : cos (- (Real.pi / 2)) = 0 := by
      rw [show - (Real.pi / 2) = - (Real.pi / 2) by ring]
      have : cos (- (Real.pi / 2)) = cos (Real.pi / 2) := by rw [cos_neg]
      rw [this, h2]
    simp [h1, h2, h3, h4] at h
    all_goals linarith [Real.pi_pos]
  constructor
  · -- f is not odd
    intro h
    specialize h 1
    rw [hf] at h
    norm_num at h
    all_goals norm_num at h
  · -- g is not odd
    intro h
    specialize h 0
    rw [hg] at h
    simp at h
    all_goals norm_num at h