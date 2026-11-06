import Mathlib

open Real Set

theorem algebra_346 :
  IsLeast {x : ℝ | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a * b = 1 ∧ x = 1 / (1 + a) + 1 / (1 + 2 * b)} (2 * √2 - 2) := by
  constructor
  · -- Show that 2 * √2 - 2 is in the set.
    use Real.sqrt 2, Real.sqrt 2 / 2
    constructor
    · -- Show a > 0 
      have h1 : Real.sqrt 2 > 0 := by positivity
      norm_num [h1]
    constructor
    · -- Show b > 0 
      have h1 : Real.sqrt 2 > 0 := by positivity 
      positivity 
    constructor
    · -- Show a * b = 1
      have h1 : Real.sqrt 2 > 0 := by positivity 
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [show Real.sqrt 2 ≠ 0 by positivity]
      <;> nlinarith
    · -- Show x = 1/(1+a) + 1/(1+2*b)
      have h1 : Real.sqrt 2 > 0 := by positivity 
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hx_eq : 1 / (1 + Real.sqrt 2) + 1 / (1 + 2 * (Real.sqrt 2 / 2)) = 2 * Real.sqrt 2 - 2 := by
        have h6 : (1 / (1 + Real.sqrt 2) + 1 / (1 + 2 * (Real.sqrt 2 / 2)) ) = 2 / (1 + Real.sqrt 2) := by
          field_simp 
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h7 : 2 / (1 + Real.sqrt 2) = 2 * Real.sqrt 2 - 2 := by
          field_simp [(show (1 + Real.sqrt 2) ≠ 0 by positivity)]
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
        rw [h6, h7]
      linarith [hx_eq]
  · -- Show that 2 * √2 - 2 is the least element in the set.
    intro x hx 
    rcases hx with ⟨a, b, ha, hb, hab, hx⟩
    have eq1 : 1 / (1 + a) + 1 / (1 + 2 * b) ≥ 2 * Real.sqrt 2 - 2 := by 
      have h4 : b = 1 / a := by 
        have hab' : a * b = 1 := hab
        have hne : a ≠ 0 := by linarith 
        field_simp [hne]
        <;> nlinarith 
      rw [h4]
      have h5 : (1 / (1 + a) + 1 / (1 + 2 * (1 / a)) ) = (1 / (1 + a) + a / (a + 2)) := by 
        field_simp 
        <;> nlinarith 
      rw [h5]
      have h5 : 0 < a := by linarith 
      have h6 : 0 < a + 2 := by nlinarith 
      have h7 : 0 < (1 + a) * (a + 2) := by nlinarith 
      have h11 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h12 : (1 / (1 + a) + a / (a + 2) ) ≥ 2 * Real.sqrt 2 - 2 := by 
        have h13 : (1 / (1 + a) + a / (a + 2) - (2 * Real.sqrt 2 - 2)) ≥ 0 := by 
          have h40 : 1 / (1 + a) + a / (a + 2) - (2 * Real.sqrt 2 - 2) = ((a + 2 + a * (1 + a) - (2 * Real.sqrt 2 - 2) * ( (1 + a) * (a + 2) )) / ( (1 + a) * (a + 2) ) ) := by 
            field_simp 
            ring 
          rw [h40]
          have h41 : a + 2 + a * (1 + a) - (2 * Real.sqrt 2 - 2) * ( (1 + a) * (a + 2) ) ≥ 0 := by 
            nlinarith [sq_nonneg (a - Real.sqrt 2), sq_nonneg ((1 + a) - (1 + Real.sqrt 2)), sq_nonneg (a + 2 - (Real.sqrt 2 + 2)), sq_nonneg (a * (a - Real.sqrt 2)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a * (a - Real.sqrt 2)), sq_nonneg ((1 + a) * (a - Real.sqrt 2)), sq_nonneg ((a + 2) * (a - Real.sqrt 2))]
          have h42 : ( (1 + a) * (a + 2) ) > 0 := by positivity 
          apply div_nonneg 
          linarith 
          all_goals positivity 
        linarith 
      linarith
    linarith [hx, eq1]