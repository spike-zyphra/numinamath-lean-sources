import Mathlib

theorem algebra_625547 (a b : ℤ) (ha: 0 < a) (hb: 0 < b): a + (a + b) * (a + b - 1) / (2:ℝ) = 2009 ↔ (a=56 ∧ b=7) := by
  constructor
  · -- Assume the equation holds, prove (a=56 ∧ b=7)
    intro h
    have eq1 : (2 * (a : ℝ) + (a + b : ℝ) * ((a + b) - 1)) = 4018 := by
      field_simp at h ⊢
      nlinarith
    have eq2 : 2 * a + (a + b) * ((a + b) - 1) = 4018 := by
      exact_mod_cast eq1

    have h3 : (a + b : ℤ) ≤ 100 := by
      nlinarith [sq_nonneg ((a + b : ℤ) - 63 : ℤ), sq_nonneg ((a : ℤ) - 56 : ℤ), sq_nonneg ((b : ℤ) - 7 : ℤ)]
    have h4 : (a + b : ℤ) ≥ 0 := by
      omega
    have h5 : (a + b : ℤ) = 63 := by 
      have h6 : (a + b : ℤ) ≤ 100 := h3
      have h7 : (a + b : ℤ) ≥ 0 := h4 
      have eq3 : 2 * a + (a + b) * ((a + b) - 1) = 4018 := by 
        linarith [eq2]
      have h10 : (a + b : ℤ) = 63 := by 
        interval_cases h9 : (a + b : ℤ) <;> omega 
      tauto 
    have h8 : b = 7 := by 
      have eq4 : 2 * a + (a + b) * ((a + b) - 1) = 4018 := by 
        linarith [eq2] 
      rw [show (a + b : ℤ) = 63 by linarith [h5] ] at eq4 
      nlinarith 
    have h9 : a = 56 := by 
      have h8' : (a + b : ℤ) = 63 := h5 
      have h8'' : b = 7 := by 
        linarith [h8] 
      omega 
    constructor 
    · linarith [h9] 
    · linarith [h8] 
  · -- Assume (a=56 ∧ b=7), prove the equation 
    rintro ⟨ha, hb⟩ 
    rw [ha, hb]
    norm_num