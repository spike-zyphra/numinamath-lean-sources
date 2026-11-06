import Mathlib

theorem inequalities_258473 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^b > b^a) (h2 : b^c > c^b) : a^c > c^a := by

  by_contra h 
  -- Assume that a^c ≤ c^a, which contradicts the conclusion we want to prove
  have h3 : a ^ c ≤ c ^ a := by linarith

  have h4 : b * (Real.log a) > a * (Real.log b) := by 
    have h1' : a ^ b > b ^ a := h1
    have pos1 : (a ^ b : ℝ) > 0 := by positivity 
    have pos2 : (b ^ a : ℝ) > 0 := by positivity 
    have h6 : a ^ b = Real.exp (b * (Real.log a)) := by
      rw [Real.rpow_def_of_pos ha]
      field_simp
      all_goals linarith 
    have h7 : b ^ a = Real.exp (a * (Real.log b)) := by 
      rw [Real.rpow_def_of_pos hb]
      field_simp 
      all_goals linarith 
    have h8 : Real.exp (b * (Real.log a)) > Real.exp (a * (Real.log b)) := by
      linarith [h1', h6, h7] 
    by_contra h
    push_neg at h 
    have h9 : Real.exp (b * (Real.log a)) ≤ Real.exp (a * (Real.log b)) := by 
      have h10 : (b * (Real.log a) : ℝ) ≤ (a * (Real.log b) : ℝ) := by nlinarith [h]
      have h11 : Real.exp ((b * (Real.log a) : ℝ)) ≤ Real.exp ((a * (Real.log b) : ℝ)) := by 
        apply Real.exp_le_exp_of_le
        linarith 
      linarith 
    linarith 

  have h5 : c * (Real.log b) > b * (Real.log c) := by 
    have h2' : b ^ c > c ^ b := h2 
    have pos1 : (b ^ c : ℝ) > 0 := by positivity 
    have pos2 : (c ^ b : ℝ) > 0 := by positivity 
    have h6 : b ^ c = Real.exp (c * (Real.log b)) := by 
      rw [Real.rpow_def_of_pos hb]
      field_simp 
      all_goals linarith 
    have h7 : c ^ b = Real.exp (b * (Real.log c)) := by 
      rw [Real.rpow_def_of_pos hc]
      field_simp 
      all_goals linarith 
    have h8 : Real.exp (c * (Real.log b)) > Real.exp (b * (Real.log c)) := by 
      linarith [h2', h6, h7] 
    by_contra h 
    push_neg at h 
    have h9 : Real.exp (c * (Real.log b)) ≤ Real.exp (b * (Real.log c)) := by 
      have h10 : (c * (Real.log b) : ℝ) ≤ (b * (Real.log c) : ℝ) := by nlinarith [h]
      have h11 : Real.exp ((c * (Real.log b) : ℝ)) ≤ Real.exp ((b * (Real.log c) : ℝ)) := by 
        apply Real.exp_le_exp_of_le 
        linarith 
      linarith 
    linarith

  have h6 : c * (Real.log a) ≤ a * (Real.log c) := by 
    have h3' : a ^ c ≤ c ^ a := h3 
    have pos1 : (a ^ c : ℝ) > 0 := by positivity 
    have pos2 : (c ^ a : ℝ) > 0 := by positivity 
    have h6 : a ^ c = Real.exp (c * (Real.log a)) := by 
      rw [Real.rpow_def_of_pos ha]
      field_simp 
      all_goals linarith 
    have h7 : c ^ a = Real.exp (a * (Real.log c)) := by 
      rw [Real.rpow_def_of_pos hc]
      field_simp 
      all_goals linarith 
    have h8 : Real.exp (c * (Real.log a)) ≤ Real.exp (a * (Real.log c)) := by 
      linarith [h3', h6, h7] 
    by_contra h 
    push_neg at h 
    have h9 : Real.exp (c * (Real.log a)) > Real.exp (a * (Real.log c)) := by 
      have h10 : (c * (Real.log a) : ℝ) > (a * (Real.log c) : ℝ) := by nlinarith [h]
      have h11 : Real.exp ((c * (Real.log a) : ℝ)) > Real.exp ((a * (Real.log c) : ℝ)) := by 
        apply Real.exp_strictMono 
        linarith 
      linarith 
    linarith 

  have h9 : (Real.log a) / a > (Real.log b) / b := by 
    have h4' : b * (Real.log a) > a * (Real.log b) := h4 
    have hb' : 0 < b := hb 
    have ha' : 0 < a := ha 
    have h10 : a > 0 := by linarith [ha']
    have h11 : b > 0 := by linarith [hb']
    have hb1 : a * b > 0 := mul_pos ha hb 
    have h12 : (b * (Real.log a)) / (a * b) > (a * (Real.log b)) / (a * b) := by 
      apply (div_lt_div_right (hb1)).mpr 
      linarith 
    have h13 : (b * (Real.log a)) / (a * b) = (Real.log a) / a := by 
      field_simp 
      <;> ring 
    have h14 : (a * (Real.log b)) / (a * b) = (Real.log b) / b := by 
      field_simp 
      <;> ring 
    linarith [h12, h13, h14] 

  have h10' : (Real.log b) / b > (Real.log c) / c := by 
    have h5 : c * (Real.log b) > b * (Real.log c) := h5 
    have hb' : 0 < b := hb 
    have hc' : 0 < c := hc 
    have hb1 : b > 0 := by linarith [hb']
    have hc1 : c > 0 := by linarith [hc']
    have hb1 : b * c > 0 := mul_pos hb hc 
    have h12 : (c * (Real.log b)) / (b * c) > (b * (Real.log c)) / (b * c) := by 
      apply (div_lt_div_right (hb1)).mpr 
      linarith 
    have h13 : (c * (Real.log b)) / (b * c) = (Real.log b) / b := by 
      field_simp 
      <;> ring 
    have h14 : (b * (Real.log c)) / (b * c) = (Real.log c) / c := by 
      field_simp 
      <;> ring 
    linarith [h12, h13, h14] 

  have h99 : (Real.log a) / a > (Real.log c) / c := by 
    linarith [h9, h10'] 

  have h100 : (Real.log a) / a ≤ (Real.log c) / c := by 
    have h6' : c * (Real.log a) ≤ a * (Real.log c) := h6 
    have ha' : 0 < a := ha 
    have hc' : 0 < c := hc 
    have h10 : a > 0 := by linarith 
    have h11 : c > 0 := by linarith 
    have h20 : a * c > 0 := mul_pos ha hc 
    have h12 : (c * (Real.log a)) / (a * c) ≤ (a * (Real.log c)) / (a * c) := by 
      apply (div_le_div_right (h20)).mpr 
      linarith 
    have h13 : (c * (Real.log a)) / (a * c) = (Real.log a) / a := by 
      field_simp 
      <;> ring 
    have h14 : (a * (Real.log c)) / (a * c) = (Real.log c) / c := by 
      field_simp 
      <;> ring 
    linarith [h12, h13, h14] 

  linarith