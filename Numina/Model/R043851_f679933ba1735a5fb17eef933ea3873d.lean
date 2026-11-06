import Mathlib

theorem algebra_144427 (f : ℝ → ℝ) :
    (∀ x y z, (f (x * y) / 2) + (f (x * z) / 2) - (f x) * (f (y * z)) ≥ 1 / 4) ↔
    ∀ x, f x = 1 / 2 := by
  constructor
  · -- Assume the inequality holds, prove that f is constant 1/2
    intro h
    have h1 : f 1 = 1 / 2 := by
      specialize h 1 1 1
      norm_num at h
      nlinarith [sq_nonneg (f 1 - 1 / 2)]
    have h0 : f 0 = 1 / 2 := by 
      specialize h 0 0 0
      norm_num at h
      nlinarith [sq_nonneg (f 0 - 1 / 2)]
    have h2 : ∀ x : ℝ, f x ≤ 1 / 2 := by 
      intro x 
      specialize h x 0 0 
      norm_num [show f 0 = 1 / 2 by linarith [h0]] at h 
      linarith 
    have h3 : ∀ x : ℝ, f x ≥ 1 / 2 := by 
      intro x 
      specialize h x 1 1 
      have h4 : f 1 = 1 / 2 := h1 
      norm_num [show f 1 = 1 / 2 by linarith [h4]] at h 
      linarith
    intro x
    linarith [h2 x, h3 x]
  · -- Assume f is constant 1/2, prove the inequality
    intro hf x y z 
    have hfx : f (x * y) = 1 / 2 := by 
      specialize hf (x * y)
      simpa using hf
    have hfy : f (x * z) = 1 / 2 := by 
      specialize hf (x * z)
      simpa using hf
    have hfxz : f x = 1 / 2 := by 
      specialize hf x 
      simpa using hf 
    have hfyz : f (y * z) = 1 / 2 := by 
      specialize hf (y * z)
      simpa using hf 
    rw [hfx, hfy, hfxz, hfyz]
    norm_num
    <;> nlinarith