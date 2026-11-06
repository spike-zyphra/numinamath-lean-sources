import Mathlib

theorem algebra_163652 (α : ℝ) :
    2 * (Real.cos (2 * α))^2 + Real.sqrt 3 * Real.sin (4 * α) - 1 =
    2 * Real.cos (Real.pi / 3 - 4 * α) := by 
  have h1 : 2 * (Real.cos (2 * α))^2 = 1 + Real.cos (4 * α) := by 
    have h2 : Real.cos (4 * α) = 2 * Real.cos (2 * α)^2 - 1 := by
      rw [show 4 * α = 2 * (2 * α) by ring]
      exact Real.cos_two_mul (2 * α)
    linarith 
  have h3 : 2 * Real.cos (Real.pi / 3 - 4 * α) = 
          2 * ( Real.cos (Real.pi / 3) * Real.cos (4 * α) + Real.sin (Real.pi / 3) * Real.sin (4 * α) ) := by 
        rw [Real.cos_sub]
  have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three 
  have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by 
    have h6 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    linarith 
  rw [h1] 
  rw [h3, h4, h5]
  <;> ring_nf <;> simp_all 
  <;> ring_nf <;> simp_all
  <;> try { tauto }
  <;> nlinarith 
  <;> try { tauto }
  <;> nlinarith 
  <;> try { tauto }
  <;> nlinarith