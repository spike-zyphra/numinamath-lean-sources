import Mathlib

theorem algebra_317014 (z1 z2 z3 : ℂ) (h₁ : ‖z1‖ = Real.sqrt 2) (h₂ : ‖z2‖ = Real.sqrt 2)
    (h₃ : z1.re * z2.re + z1.im * z2.im = 0) (h₄ : ‖z1 + z2 - z3‖ = 1) :
    1 ≤ ‖z3‖ ∧ ‖z3‖ ≤ 3 := by

  have h13 : z1.re ^ 2 + z1.im ^ 2 = 2 := by 
    have h14 : ‖z1‖ = Real.sqrt 2 := h₁ 
    have h15 : ‖z1‖ = Real.sqrt ((z1.re) ^ 2 + (z1.im) ^ 2) := by 
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring
    rw [h14] at h15 
    rw [Real.sqrt_inj (by positivity) (by positivity) ] at h15 
    linarith
  
  have h14 : z2.re ^ 2 + z2.im ^ 2 = 2 := by 
    have h15 : ‖z2‖ = Real.sqrt 2 := h₂ 
    have h16 : ‖z2‖ = Real.sqrt ((z2.re) ^ 2 + (z2.im) ^ 2) := by 
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring
    rw [h15] at h16 
    rw [Real.sqrt_inj (by positivity) (by positivity) ] at h16 
    linarith 

  have h7 : ‖z1 + z2‖ = 2 := by 
    have h8 : ‖z1 + z2‖ = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by 
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring 
    have h9 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = 4 := by
      nlinarith [h₃, h13, h14]

    rw [h8]
    rw [h9]
    have h10 : Real.sqrt ((4 : ℝ)) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    rw [h10] 

  have h8 : 1 ≤ ‖z3‖ := by 
    have h9 : (z1 + z2) - (z1 + z2 - z3) = z3 := by 
      ring_nf 
    have h10 : ‖(z1 + z2) - (z1 + z2 - z3)‖ ≥ ‖z1 + z2‖ - ‖z1 + z2 - z3‖ := by 
      apply norm_sub_norm_le 
    have h11 : ‖(z1 + z2) - (z1 + z2 - z3)‖ = ‖z3‖ := by 
      rw [h9] 
    nlinarith [h10, h7, h₄, h11]

  have h9 : ‖z3‖ ≤ 3 := by 
    have eq1 : ‖z3‖ = ‖(z1 + z2) - (z1 + z2 - z3)‖ := by 
      have eq2 : (z1 + z2) - (z1 + z2 - z3) = z3 := by 
        ring_nf 
      rw [eq2] 
    have eq2 : ‖(z1 + z2) - (z1 + z2 - z3)‖ ≤ ‖z1 + z2‖ + ‖z1 + z2 - z3‖ := by 
      apply norm_sub_le 
    have eq3 : ‖z3‖ ≤ ‖z1 + z2‖ + ‖z1 + z2 - z3‖ := by 
      rw [eq1] 
      linarith 
    nlinarith [h₄, h7, eq3]

  constructor 
  · exact h8 
  · exact h9