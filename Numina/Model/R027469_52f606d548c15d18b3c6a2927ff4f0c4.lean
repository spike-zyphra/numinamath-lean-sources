import Mathlib

theorem algebra_207547 (f : ℝ → ℝ) :
    (∀ x y z, (1/2)*f (x*y) + (1/2)*f (x*z) - f x * f (y*z) ≥ 1/4) ↔
    ∀ x, f x = 1/2 := by
  constructor
  · -- Forward: if $f$ satisfies the inequality then $f(x) = \frac{1  }{2}$ for all $x$
    intro h
    -- First, let's determine f(0) by substituting x = 0:
    have h0 : f 0 = 1 / 2 := by
      have h1 := h 0 0 0 
      simp at h1
      have h2 : (f 0 - 1 / 2) ^ 2 ≤ 0 := by nlinarith
      have h3 : f 0 - 1 / 2 = 0 := by nlinarith [sq_nonneg (f 0 - 1 / 2)]
      linarith
    -- Substitute y = 0 to get f(xz) ≥ f(x)
    have h_subst1 : ∀ x z : ℝ, f (x * z) ≥ f x := by
      intro x z
      specialize h x 0 z 
      simp [h0] at h 
      nlinarith 
    -- For any x, set z = 0 in h_subst1: f(0) ≥ f(x)
    have h1 : ∀ x : ℝ, f x ≤ 1 / 2 := by
      intro x
      specialize h_subst1 x 0 
      simp [h0] at h_subst1 
      linarith 
    -- Substitute (x,1,1) to get f(x) ≥ 1/2
    have h2 : f 1 = 1 / 2 := by 
      have h11 := h 1 1 1 
      simp at h11 
      have h12 : (f 1 - 1 / 2) ^ 2 ≤ 0 := by nlinarith 
      have h13 : f 1 - 1 / 2 = 0 := by nlinarith [sq_nonneg (f 1 - 1 / 2)]
      linarith 
    -- Substitute (x,1,1) to get f(x) - f(x)f(1) ≥ 1/4
    have h3 : ∀ x : ℝ, f x ≥ 1 / 2 := by
      intro x
      specialize h x 1 1 
      simp [h2] at h 
      linarith 
    -- Now conclude f(x) = 1/2 for all x
    intro x
    have hx1 := h1 x 
    have hx2 := h3 x 
    linarith 
  · -- Backward: if f(x) = 1/2 for all x, then the inequality holds
    intro hf x y z 
    have h1 : f (x * y) = 1 / 2 := by apply hf 
    have h2 : f (x * z) = 1 / 2 := by apply hf 
    have h3 : f x = 1 / 2 := by apply hf 
    have h4 : f (y * z) = 1 / 2 := by apply hf 
    rw [h1, h2, h3, h4] 
    norm_num