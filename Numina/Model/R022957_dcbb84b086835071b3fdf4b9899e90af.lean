import Mathlib

theorem number_theory_235230 (R : ℝ) (hR : R = Real.sqrt 1105) :
    Set.ncard {p : ℤ × ℤ | p.1^2 + p.2^2 = R^2} = 32 := by
  have h1 : R ^ 2 = 1105 := by
    rw [hR]
    rw [Real.sq_sqrt]
    all_goals norm_num
  have h2 : {p : ℤ × ℤ | p.1^2 + p.2^2 = R^2} = {p : ℤ × ℤ | p.1^2 + p.2^2 = 1105} := by 
    ext ⟨a, b⟩
    simp [h1]
    <;> norm_cast
    all_goals norm_num
  rw [h2]
  have h3 : {p : ℤ × ℤ | p.1^2 + p.2^2 = 1105} = Finset.filter (fun p : ℤ × ℤ => p.1^2 + p.2^2 = 1105) (Finset.Icc ( (-33 : ℤ) , (-33) ) ( (33 : ℤ), (33) ) ) := by
    ext ⟨a, b⟩
    simp
    intro h_eq
    have h2 : a^2 + b^2 = 1105 := by
      linarith
    have h3 : a ≤ 33 := by nlinarith
    have h4 : a ≥ -33 := by nlinarith
    have h5 : b ≤ 33 := by nlinarith
    have h6 : b ≥ -33 := by nlinarith
    simp [h3, h4, h5, h6]
    <;> linarith
  rw [h3]
  rw [Set.ncard_coe_Finset]
  native_decide