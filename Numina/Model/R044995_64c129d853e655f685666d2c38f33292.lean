import Mathlib

theorem other_47890 {f : ℝ → ℝ → ℝ} (hf : ∀ x y u, f (x + u) (y + u) = f x y + u)
    (hf' : ∀ x y v, f (x * v) (y * v) = f x y * v) :
    ∃ p q, ∀ x y, f x y = p * x + q * y ∧ p + q = 1 := by

  have h1 : f 0 0 = 0 := by
    specialize hf' 0 0 0
    norm_num at hf'
    linarith
  
  have h2 : ∀ u, f u u = u := by
    intro u
    specialize hf 0 0 u
    simp [h1] at hf
    linarith
  
  have h3 : ∀ v, f v 0 = f 1 0 * v := by
    intro v
    specialize hf' 1 0 v
    norm_num at hf'
    linarith
  
  have h5 : ∀ x y, f x y = f 1 0 * x + (1 - f 1 0) * y := by
    intro x y
    specialize hf x y (-y)
    have h6 : f (x + (-y)) (y + (-y)) = f x y + (-y) := hf
    have h7 : f (x - y) 0 = f x y - y := by 
      simp [show x + (-y) = x - y by ring, show y + (-y) = (0 : ℝ) by ring] at h6
      linarith

    have h8 : f (x - y) 0 = f 1 0 * (x - y) := h3 (x - y)
    
    rw [h8] at h7
    linarith

  use f 1 0 
  use 1 - f 1 0 
  intro x y 
  constructor
  · -- Show f x y = f 1 0 * x + (1 - f 1 0) * y 
    specialize h5 x y 
    linarith 
  · -- Show f 1 0 + (1 - f 1 0) = 1 
    linarith