import Mathlib

theorem inequalities_45598 (f : ℝ → ℝ) (hle : ∀ x, f x ≤ x)
    (hadd : ∀ x y, f (x + y) ≤ f x + f y) : ∀ x, f x = x := by
  have h1 : f 0 = 0 := by
    have hadd_0 : f (0 + 0) ≤ f 0 + f 0 := hadd 0 0
    have h1_le : f 0 ≤ 0 := hle 0
    norm_num at hadd_0
    linarith [hadd_0, h1_le]
  have h2 : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    have h5 := hadd x (-x : ℝ)
    have h4 : f (x + (-x : ℝ)) = f 0 := by ring_nf
    rw [h4] at h5
    have h3 : f x ≤ x := hle x
    have h4 : f (-x) ≤ -x := hle (-x)
    have h5' : f x + f (-x) ≥ 0 := by linarith [h5, h1]
    have h6 : f x + f (-x) ≤ 0 := by linarith [h3, h4]
    have h7 : f x + f (-x) = 0 := by linarith
    linarith 
  intro x
  have h5 : f x ≤ x := hle x
  have h6 : f (-x) ≤ -x := hle (-x)
  have h2_x : f (-x) = -f x := h2 x
  have h8 : f x ≥ x := by linarith [h2_x, h6]
  linarith [h5, h8]