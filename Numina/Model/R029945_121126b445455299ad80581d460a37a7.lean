import Mathlib

theorem algebra_12628 (f : ℝ → ℝ) (hf : f = fun b => (1/2)*b^2 + 5*b - 3) :
    IsLeast (Set.range f) (f (-5)) := by
  have h1 : ∀ b, f b = (1 / 2) * b ^ 2 + 5 * b - 3 := by 
    intro b
    rw [hf]
  have h2 : f (-5) = -31 / 2 := by 
    rw [h1]
    norm_num
  constructor
  · -- First, show that f(-5) is in the range of f
    simpa using by norm_num
  · -- Now, show that f(-5) is the smallest value in the range
    intro y hy
    rcases hy with ⟨b, hb⟩
    have h3 : f b = (1 / 2) * b ^ 2 + 5 * b - 3 := by 
      apply h1
    have h5 : f b = (1 / 2) * (b + 5) ^ 2 - 31 / 2 := by
      rw [h1]
      ring_nf
    have h6 : f (-5) ≤ f b := by 
      rw [h2]
      rw [h5]
      have h7 : (1 / 2 : ℝ) * (b + 5) ^ 2 ≥ 0 := by 
        apply mul_nonneg 
        norm_num 
        apply pow_two_nonneg 
      linarith 
    linarith [h6, hb]