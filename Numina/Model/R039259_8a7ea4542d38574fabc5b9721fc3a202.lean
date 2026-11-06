import Mathlib

theorem algebra_200523 {f : ℝ → ℝ} (hf : ∀ x y, f (x * y) = f x * f y - f x - f y + 2)
    (hf' : ∀ x y, f (x + y) = f x + f y + 2 * x * y - 1) (hf'' : f 1 = 2) :
    ∀ x, f x = x ^ 2 + 1 := by
  have f0 : f 0 = 1 := by
    have h1 := hf' 0 0
    norm_num at h1
    linarith
  intro x
  have eq1 : f (x + 1) = f x + 2 * x + 1 := by
    specialize hf' x 1
    simp [hf''] at hf'
    linarith
  have f2 : f 2 = 5 := by
    specialize hf' 1 1
    norm_num [hf''] at hf'
    linarith
  have eq4 : f (2 * x) = 4 * f x - 3 := by
    specialize hf 2 x
    rw [f2] at hf
    linarith
  have eq5 : f (2 * x) = 2 * f x + 2 * x ^ 2 - 1 := by
    have h1 : f (x + x) = f x + f x + 2 * x * x - 1 := by
      apply hf' 
    have h2 : f (x + x) = f (2 * x) := by
      ring_nf
    rw [h2] at h1
    linarith
  have eq6 : 2 * f x = 2 * x ^ 2 + 2 := by
    linarith [eq4, eq5]
  linarith