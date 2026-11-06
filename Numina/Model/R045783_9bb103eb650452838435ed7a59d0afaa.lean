import Mathlib

theorem algebra_609336 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + 6 * x + 7) :
    IsLeast {y | ∃ x, y = f (f (f (f x)))} 23 := by
  constructor
  · -- First part showing it's achieved
    use -3
    norm_num [hf]
  · -- Second part: proving minimality
    intro y hy
    rcases hy with ⟨x, h_eq⟩
    rw [h_eq]
    have h1 : ∀ x, f x = x ^ 2 + 6 * x + 7 := hf
    have h2 : ∀ (t : ℝ), f t ≥ -2 := by 
      intro t 
      have h1' : f t = t ^ 2 + 6 * t + 7 := h1 t 
      rw [h1']
      nlinarith [sq_nonneg (t + 3)]
    have h4 : ∀ x, f (f (f (f x))) ≥ 23 := by 
      intro x 
      have h2f1 : f x ≥ -2 := h2 x 
      have h2f2 : f (f x) ≥ -1 := by 
        have h2f2 : f x ≥ -2 := h2f1
        have h5 : f (f x) ≥ -1 := by 
          have h1' : f (f x) = (f x) ^ 2 + 6 * (f x) + 7 := by 
            apply hf 
          rw [h1']
          nlinarith [sq_nonneg (f x + 3)]
        linarith 
      have h2f3 : f (f (f x)) ≥ 2 := by 
        have h2f3 : f (f x) ≥ -1 := h2f2
        have h3 : f (f (f x)) ≥ 2 := by 
          have h1' : f (f (f x)) = (f (f x)) ^ 2 + 6 * (f (f x)) + 7 := by 
            apply hf 
          rw [h1']
          nlinarith [sq_nonneg (f (f x) + 3)]
        linarith 
      have h2f4 : f (f (f (f x))) ≥ 23 := by 
        have h2f4 : f (f (f x)) ≥ 2 := h2f3 
        have h4 : f (f (f (f x))) ≥ 23 := by 
          have h1' : f (f (f (f x))) = (f (f (f x))) ^ 2 + 6 * (f (f (f x))) + 7 := by 
            apply hf 
          rw [h1']
          nlinarith [sq_nonneg (f (f (f x)) + 3)]
        linarith 
      linarith 
    specialize h4 x 
    linarith