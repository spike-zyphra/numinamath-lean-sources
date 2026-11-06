import Mathlib
/-if the function f x =x / ((2 * x + 1) * (x - a)) is odd, then a=?-/
theorem algebra_601311 {f : ℝ → ℝ} (hf : f = fun x => x / ((2 * x + 1) * (x - a))) (ha : ∀ x, f (-x) = -f x) :
    a = 1 / 2 := by
  -- prove by evaluating on particular points 
  have h1 := ha 1
  rw [hf] at h1
  norm_num at h1
  have h2 := ha 2
  rw [hf] at h2
  norm_num at h2
  have h3 := ha (3 : ℝ)
  rw [hf] at h3
  norm_num at h3
  have h4 := ha (1 / 2 : ℝ)
  rw [hf] at h4
  norm_num at h4
  have h5 := ha (1 / 3 : ℝ)
  rw [hf] at h5
  norm_num at h5
  have h6 := ha (-1 : ℝ)
  rw [hf] at h6
  norm_num at h6
  nlinarith