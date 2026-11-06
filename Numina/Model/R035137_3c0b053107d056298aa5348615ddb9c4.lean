import Mathlib

theorem algebra_218182 (z1 z2 : ℂ) (h₀ : ‖z1‖ = 1) (h₁ : ‖z2‖ = 1)
    (h₂ : ‖z1 + z2‖ = Real.sqrt 2) :
    ‖z1 - z2‖ = Real.sqrt 2 := by
  have h3 : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring_nf
  have h4 : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring_nf
  have h5 : ‖z1 + z2‖ = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring_nf
  have h6 : ‖z1 - z2‖ = Real.sqrt ((z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.sub_re, Complex.sub_im]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring_nf
  have h7 : z1.re ^ 2 + z1.im ^ 2 = 1 := by 
    rw [h3] at h₀ 
    have h8 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = 1 := h₀
    have h9 : z1.re ^ 2 + z1.im ^ 2 = 1 := by
      calc 
        z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by rw [h8]
        _ = 1 := by norm_num
    exact h9
  have h10 : z2.re ^ 2 + z2.im ^ 2 = 1 := by 
    rw [h4] at h₁ 
    have h11 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = 1 := h₁
    have h12 : z2.re ^ 2 + z2.im ^ 2 = 1 := by
      calc 
        z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by rw [h11]
        _ = 1 := by norm_num
    exact h12
  have h13 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = 2 := by
    rw [h5] at h₂
    have h14 : Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) = Real.sqrt 2 := h₂
    have h15 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 = 2 := by
      rw [Real.sqrt_inj (by positivity) (by positivity) ] at h14
      linarith
    exact h15
  have h17 : (z1.re - z2.re) ^ 2 + (z1.im - z2.im) ^ 2 = 2 := by 
    nlinarith [h7, h10, h13]
  rw [h6]
  rw [h17]
  all_goals norm_num