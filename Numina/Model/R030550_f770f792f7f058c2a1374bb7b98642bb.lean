import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_16836 {f : ℝ → ℝ} (hf : f = λ x => cos x + cos (3 * x) + cos (7 * x) + cos (9 * x)) :
    ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
      ∀ x, f x = a * cos (b * x) * cos (c * x) * cos (d * x) := by 
  use 4, 1, 3, 5
  constructor
  · norm_num -- a > 0
  constructor
  · norm_num -- b > 0
  constructor
  · norm_num -- c > 0
  constructor
  · norm_num -- d > 0
  intro x
  rw [hf]
  have eq1 : cos x + cos (3 * x) + cos (7 * x) + cos (9 * x) = 4 * cos x * cos (3 * x) * cos (5 * x) := by
    have eq2 : cos x + cos (9 * x) = 2 * cos (5 * x) * cos (4 * x) := by 
      have h1 : cos x + cos (9 * x) = 2 * cos ((x + 9 * x) / 2) * cos ((x - 9 * x) / 2) := by
        rw [cos_add_cos]
      have h2 : (x + 9 * x) / 2 = 5 * x := by ring_nf 
      have h3 : (x - 9 * x) / 2 = -4 * x := by ring_nf 
      rw [h2, h3] at h1
      have h4 : cos (-4 * x) = cos (4 * x) := by 
        have h5 : cos (-4 * x) = cos (4 * x) := by 
          rw [show -4 * x = - (4 * x) by ring]
          rw [cos_neg]
        linarith [h5]
      have eq3 : cos x + cos (9 * x) = 2 * cos (5 * x) * cos (4 * x) := by 
        have eq4 : cos x + cos (9 * x) = 2 * cos (5 * x) * cos (-4 * x) := by 
          linarith [h1]
        rw [h4] at eq4 
        linarith [eq4]
      linarith [eq3]
    have eq3 : cos (3 * x) + cos (7 * x) = 2 * cos (5 * x) * cos (2 * x) := by 
      have h1 : cos (3 * x) + cos (7 * x) = 2 * cos ((3 * x + 7 * x) / 2) * cos ((3 * x - 7 * x) / 2) := by 
        rw [cos_add_cos]
      have h2 : (3 * x + 7 * x) / 2 = 5 * x := by ring_nf 
      have h3 : (3 * x - 7 * x) / 2 = -2 * x := by ring_nf 
      have h4 : cos (-2 * x) = cos (2 * x) := by 
        have h5 : cos (-2 * x) = cos (2 * x) := by 
          rw [show -2 * x = - (2 * x) by ring]
          rw [cos_neg]
        linarith [h5]
      rw [h2, h3] at h1 
      have eq4 : cos (3 * x) + cos (7 * x) = 2 * cos (5 * x) * cos (2 * x) := by 
        have eq5 : cos (3 * x) + cos (7 * x) = 2 * cos (5 * x) * cos (-2 * x) := by 
          linarith [h1]
        rw [h4] at eq5 
        linarith [eq5]
      linarith [eq4]
    have eq4 : cos x + cos (3 * x) + cos (7 * x) + cos (9 * x) = 2 * cos (5 * x) * (cos (4 * x) + cos (2 * x)) := by 
      linarith [eq2, eq3]
    have eq5 : cos (4 * x) + cos (2 * x) = 2 * cos (3 * x) * cos x := by 
      have h1 : cos (4 * x) + cos (2 * x) = 2 * cos ((4 * x + 2 * x) / 2) * cos ((4 * x - 2 * x) / 2) := by 
        rw [cos_add_cos]
      have h2 : (4 * x + 2 * x) / 2 = 3 * x := by ring_nf 
      have h3 : (4 * x - 2 * x) / 2 = x := by ring_nf 
      rw [h2, h3] at h1 
      linarith [h1]
    have eq6 : cos x + cos (3 * x) + cos (7 * x) + cos (9 * x) = 4 * cos x * cos (3 * x) * cos (5 * x) := by 
      rw [eq4]
      rw [eq5]
      ring_nf
    exact eq6
  simp [eq1]
  <;> ring_nf