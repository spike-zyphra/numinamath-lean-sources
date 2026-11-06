import Mathlib
open Classical


theorem algebra_697 (x e a b aₜ bₜ : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (he : e ≠ 0) (hat : 150 = a * aₜ) (hbt : 75 = b * bₜ) (heat : 150 - x = e * aₜ) (hebt : x - 75 = e * bₜ) (hab : a = 3 * b) : (x = 120) := by
  have h3 : 3 * b = 5 * e := by
    have eq1 : (150 - x) * b = 50 * e := by
      have h7 : (150 - x) * a = 150 * e := by
        have hea1 : 150 / a = aₜ := by 
          rw [← mul_comm] at hat 
          exact div_eq_of_eq_mul ha hat 
        have hea2 : (150 - x) / e = aₜ := by 
          rw [← mul_comm] at heat 
          exact div_eq_of_eq_mul he heat 
        have hea3 : (150 - x) / e = 150 / a := Eq.trans hea2 (Eq.symm hea1) 
        have h4 : (150 - x) * a = 150 * e := by 
          have hea4 : (150 - x) / e = 150 / a := hea3 
          field_simp [ha, he] at hea4 ⊢ 
          linarith 
        exact h4 
      rw [hab] at h7 
      linarith 
    have eq2 : (x - 75) * b = 75 * e := by 
      have hf1 : (x - 75) / 75 = e / (b : ℚ) := by 
        have hf1' : (x - 75) / e = 75 / (b : ℚ) := by 
          have heq1 : (x - 75) / e = bₜ := by 
            rw [← mul_comm] at hebt 
            exact div_eq_of_eq_mul he hebt 
          have heq2 : (75 : ℚ) / (b : ℚ) = bₜ := by 
            rw [← mul_comm] at hbt 
            exact div_eq_of_eq_mul hb hbt 
          linarith 
        have hne16 : (b : ℚ) ≠ 0 := by exact_mod_cast hb 
        have hne11 : (75 : ℚ) ≠ 0 := by norm_num 
        field_simp [hne16, hne11] at hf1' ⊢ 
        linarith 
      have hne11 : (75 : ℚ) ≠ 0 := by norm_num 
      have hne16 : (b : ℚ) ≠ 0 := by exact_mod_cast hb 
      field_simp [hne16, hne11] at hf1 ⊢ 
      linarith 
    linarith 
  have hx : x = 120 := by 
    have eq1 : (150 - x) * b = 50 * e := by 
      have h7 : (150 - x) * a = 150 * e := by
        have hea1 : 150 / a = aₜ := by 
          rw [← mul_comm] at hat 
          exact div_eq_of_eq_mul ha hat 
        have hea2 : (150 - x) / e = aₜ := by 
          rw [← mul_comm] at heat 
          exact div_eq_of_eq_mul he heat 
        have hea3 : (150 - x) / e = 150 / a := Eq.trans hea2 (Eq.symm hea1) 
        have h4 : (150 - x) * a = 150 * e := by 
          have hea4 : (150 - x) / e = 150 / a := hea3 
          field_simp [ha, he] at hea4 ⊢ 
          linarith 
        exact h4 
      rw [hab] at h7 
      linarith 
    have eq2 : (x - 75) * b = 75 * e := by 
      have hf1 : (x - 75) / 75 = e / (b : ℚ) := by 
        have hf1' : (x - 75) / e = 75 / (b : ℚ) := by 
          have heq1 : (x - 75) / e = bₜ := by 
            rw [← mul_comm] at hebt 
            exact div_eq_of_eq_mul he hebt 
          have heq2 : (75 : ℚ) / (b : ℚ) = bₜ := by 
            rw [← mul_comm] at hbt 
            exact div_eq_of_eq_mul hb hbt 
          linarith 
        have hne16 : (b : ℚ) ≠ 0 := by exact_mod_cast hb 
        have hne11 : (75 : ℚ) ≠ 0 := by norm_num 
        field_simp [hne16, hne11] at hf1' ⊢ 
        linarith 
      have hne11 : (75 : ℚ) ≠ 0 := by norm_num 
      have hne16 : (b : ℚ) ≠ 0 := by exact_mod_cast hb 
      field_simp [hne16, hne11] at hf1 ⊢ 
      linarith 
    rw [show e = (3 / 5) * b from by linarith] at eq1 eq2 
    apply (mul_left_inj' hb).mp 
    linarith 
  exact hx