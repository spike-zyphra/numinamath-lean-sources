import Mathlib

theorem algebra_264681 (A B : ℂ) (hA : ‖A‖ = 2) (hAB : A^2 - 2 * A * B + 4 * B^2 = 0) :
    dist 0 A + dist 0 B + dist A B = 3 + Real.sqrt 3 := by
  have h1 : A = B * (1 + Complex.I * Real.sqrt 3) ∨ A = B * (1 - Complex.I * Real.sqrt 3) := by
    have eq1 : A^2 - 2 * A * B + 4 * B^2 = 0 := hAB
    have eq2 : A^2 - 2 * A * B + 4 * B^2 = (A - B * (1 + Complex.I * Real.sqrt 3)) * (A - B * (1 - Complex.I * Real.sqrt 3)) := by
      ring_nf
      <;> simp [Complex.ext_iff, pow_two, Complex.I_mul_I, mul_add, sub_eq_zero]
      <;> ring_nf
      <;> norm_num [Real.sqrt_sq]
      <;> ring
    rw [eq2] at eq1
    cases (mul_eq_zero.mp eq1) with
    | inl h => 
      left
      exact eq_of_sub_eq_zero h
    | inr h => 
      right
      exact eq_of_sub_eq_zero h

  cases h1 with
  | inl hA1 =>
    have hB : ‖B‖ = 1 := by
      have hA' : ‖A‖ = 2 := hA
      have hA_eq : A = B * (1 + Complex.I * Real.sqrt 3) := by 
        exact hA1
      have hA_norm : ‖A‖ = ‖B‖ * Real.sqrt (1^2 + (Real.sqrt 3)^2) := by
        rw [hA_eq]
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        <;> ring_nf <;> norm_num [Real.sqrt_sq]
        <;> ring
      rw [hA_norm] at hA'
      have h1' : Real.sqrt (1^2 + (Real.sqrt 3)^2) = 2 := by
        have h1 : (1 : ℝ) ^ 2 + (Real.sqrt 3 : ℝ) ^ 2 = 4 := by
          have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          norm_num [h2]
        rw [h1]
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h1'] at hA'
      have hB' : ‖B‖ = 1 := by 
        nlinarith
      exact hB'

    have hAB1 : dist A B = Real.sqrt 3 := by
      have hAB' : dist A B = ‖A - B‖ := by
        simp [dist_eq_norm]
      rw [hAB']
      have hA_sub_B : A - B = B * (Complex.I * Real.sqrt 3) := by
        rw [hA1]
        ring
      have hAB_norm : ‖A - B‖ = ‖B‖ * Real.sqrt 3 := by
        rw [hA_sub_B]
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        <;> ring_nf <;> norm_num [Real.sqrt_sq]
        <;> ring
      rw [hAB_norm, hB]
      all_goals nlinarith

    have hOA : dist 0 A = 2 := by
      simp [dist_eq_norm]
      simpa [hA]

    have hOB : dist 0 B = 1 := by
      simp [dist_eq_norm]
      simpa [hB]

    linarith [hOA, hOB, hAB1]

  | inr hA2 =>
    have hB : ‖B‖  = 1 :=  by
      have  hA' : ‖A‖ = 2 := hA
      have  hA_eq : A = B * (1 -  Complex.I *  Real.sqrt 3) :=  by
        exact  hA2
      have  hA_norm : ‖A‖ = ‖B‖ * Real.sqrt (1^2 + (Real.sqrt 3)^2) :=  by
        rw [hA_eq]
        simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
        <;> ring_nf <;> norm_num [Real.sqrt_sq]
        <;> ring
      rw [hA_norm] at hA'
      have h1' :  Real.sqrt (1^2 + (Real.sqrt 3)^2) = 2 :=  by
        have  h1 : (1 : ℝ) ^ 2 + (Real.sqrt 3 : ℝ) ^ 2 = 4 :=  by
          have  h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          norm_num [h2]
        rw [h1]
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h1'] at hA'
      have hB' : ‖B‖  = 1 :=  by 
        nlinarith
      exact hB'

    have hAB2 : dist A B  = Real.sqrt 3 :=  by
      have hAB' : dist A B = ‖A - B‖ :=  by
        simp [dist_eq_norm]
      rw [hAB']
      have hA_sub_B : A - B =  B * (-Complex.I * Real.sqrt 3) :=  by
        rw [hA2]
        ring
      have hAB_norm : ‖A - B‖ = ‖B‖ * Real.sqrt 3 :=  by
        rw [hA_sub_B]
        simp [Complex.norm_eq_abs, Complex.abs,  Complex.normSq]
        <;> ring_nf <;> norm_num [Real.sqrt_sq]
        <;>  ring
      rw [hAB_norm, hB]
      all_goals nlinarith

    have hOA : dist 0 A  = 2  :=  by
      simp [dist_eq_norm]
      simpa [hA]

    have hOB : dist 0  B  = 1  :=  by
      simp [dist_eq_norm]
      simpa [hB]

    linarith [hOA, hOB, hAB2]