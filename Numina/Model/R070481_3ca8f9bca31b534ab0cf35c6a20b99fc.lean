import Mathlib

theorem algebra_145912 (f : ℝ → ℝ) (hf : f = fun x => Real.pi * Real.sin (4 * x)) :
    IsGreatest (Set.range f) Real.pi := by 
  constructor
  · -- Show π is in the range of f
    use Real.pi / 8
    simp [hf]
    have h1 : Real.sin (4 * (Real.pi / 8)) = Real.sin (Real.pi / 2) := by 
      ring_nf
    rw [h1]
    rw [Real.sin_pi_div_two]
    all_goals linarith [Real.pi_pos]
  
  · -- Show π is the greatest in the range of f
    intro y
    rintro ⟨x, hx⟩
    simp [hf] at hx 
    have h2 : Real.sin (4 * x) ≤ 1 := by 
      apply Real.sin_le_one
    nlinarith [Real.pi_pos]