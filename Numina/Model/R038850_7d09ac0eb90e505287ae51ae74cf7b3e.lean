import Mathlib

theorem algebra_271719 :
    {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | 
      (∃ diff, b = a + diff ∧ c = b + diff) ∧
      (∃ r, c = b * r ∧ d = c * r) ∧
      a + d = 37 ∧ b + c = 36} =
    {(12, 16, 20, 25), (99/4, 81/4, 63/4, 49/4)} := by 
  ext ⟨a, b, c, d⟩
  simp [-one_div]
  constructor
  · -- Assume (a, b, c, d) in the left side
    rintro ⟨⟨diff, h1a, h1b⟩, ⟨r, h1c, h1d⟩, h3a, h4a⟩
    have h_eq1 : 2 * b = a + c := by 
      linarith
    have h_eq3 : c = 36 - b := by linarith 
    have h_eq4 : a = 3 * b - 36 := by 
      linarith 
    have h_eq5 : d = 73 - 3 * b := by 
      linarith [h_eq4, h_eq3, h3a]
    have h_eq9 : c ^ 2 = b * d := by
      have eq_c : c = b * r := h1c
      have eq_d : d = c * r := h1d
      rw [eq_d]
      rw [eq_c]
      ring
    rw [h_eq3, h_eq5] at h_eq9
    have h_eq6 : 4 * b ^ 2 - 145 * b + 1296 = 0 := by
      nlinarith
    have : (b - 16) * (4 * b - 81) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp this) with h16 h81
    · -- Assume b = 16
      have hb16 : b = 16 := by linarith 
      have h_eq7 : a = 12 := by 
        rw [hb16] at h_eq4 
        linarith 
      have h_eq8 : c = 20 := by 
        rw [hb16] at h_eq3 
        linarith 
      have h_eq9 : d = 25 := by 
        rw [hb16] at h_eq5 
        linarith 
      simp [hb16, h_eq7, h_eq8, h_eq9]
    · -- Assume 4 * b - 81 = 0 ⇒ b = 81/4 
      have hb81 : b = (81 : ℝ)/4 := by linarith 
      have h_eq10 : a = (99 : ℝ)/4 := by 
        rw [hb81] at h_eq4 
        linarith 
      have h_eq11 : c = (63 : ℝ)/4 := by 
        rw [hb81] at h_eq3 
        linarith 
      have h_eq12 : d = (49 : ℝ)/4 := by 
        rw [hb81] at h_eq5 
        linarith 
      simp [hb81, h_eq10, h_eq11, h_eq12]
  · -- Assume the right side
    rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · -- Prove the four goals 
      constructor 
      · -- Arithmetic sequence 
        use 4 
        constructor 
        · -- Show b = a + 4 
          norm_num 
        · -- Show c = b + 4 
          norm_num 
      constructor 
      · -- Geometric sequence 
        use (20 / 16) 
        constructor 
        · -- Show c = b * (20 / 16) 
          norm_num 
        · -- Show d = c * (20 / 16) 
          norm_num 
      constructor 
      · -- a + d = 37 
        norm_num 
      · -- b + c = 36 
        norm_num 
    · -- Second case 
      constructor
      · -- Arithmetic sequence 
        use (81/4 - 99/4) 
        constructor 
        · -- Show b = a + (81/4 - 99/4) 
          norm_num 
        · -- Show c = b + (81/4 - 99/4) 
          norm_num 
      constructor 
      · -- Geometric sequence 
        use ( (63/4) / (81/4) ) 
        constructor 
        · -- Show c = b * ((63/4) / (81/4))
          norm_num
        · -- Show d = c * ((63/4) / (81/4))
          norm_num
      constructor 
      · -- a + d = 37 
        norm_num 
      · -- b + c = 36 
        norm_num