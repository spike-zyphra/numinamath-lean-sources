import Mathlib

theorem algebra_305510 (a b c : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : b ≠ c)
    (x y z : ℝ) (h1 : x / a^3 - y / a^2 + z / a = 1) (h2 : x / b^3 - y / b^2 + z / b = 1)
    (h3 : x / c^3 - y / c^2 + z / c = 1) :
    x = a * b * c ∧ y = a * b + b * c + c * a ∧ z = a + b + c := by

  have ha2 : a ≠ 0 := by
    by_contra h
    rw [show a = (0 : ℝ) by linarith] at h1
    norm_num [h] at h1 
    all_goals try { linarith }
    all_goals try { tauto }
    all_goals norm_num [h] at h1
  
  have hb2 : b ≠ 0 := by
    by_contra h
    rw [show b = (0 : ℝ) by linarith] at h2
    norm_num [h] at h2
    all_goals try { linarith }
    all_goals try { tauto }
    all_goals norm_num [h] at h2
  
  have hc2 : c ≠ 0 := by
    by_contra h
    rw [show c = (0 : ℝ) by linarith] at h3
    norm_num [h] at h3
    all_goals try { linarith }
    all_goals try { tauto }
    all_goals norm_num [h] at h3
  
  have eq1 : x - a * y + a^2 * z = a^3 := by
    have h1' : x / a^3 - y / a^2 + z / a = 1 := h1
    -- Multiply through by a^3 to clear denominators
    have h4 : a ≠ 0 := ha2
    have eq2' : x - a * y + a^2 * z = a^3 := by
      have eq3 : x / a^3 - y / a^2 + z / a = 1 := h1'
      have eq4 : a ≠ 0 := h4 
      have eq5 : x / a^3 - y / a^2 + z / a = (x - a * y + a^2 * z) / a^3 := by 
        field_simp [h4]
        <;> ring  -- Simplify the expression to the form (x - a*y + a^2*z)/a^3
      rw [eq5] at eq3 
      have eq6 : (x - a * y + a^2 * z) / a^3 = 1 := eq3 
      have eq7 : x - a * y + a^2 * z = a^3 := by
        field_simp [h4] at eq6 ⊢
        all_goals linarith 
      assumption 
    assumption
  
  have eq2 : x - b * y + b^2 * z = b^3 := by
    have h2' : x / b^3 - y / b^2 + z / b = 1 := h2
    -- Multiply through by b^3 to clear denominators
    have h4 : b ≠ 0 := hb2
    have eq2'2 : x - b * y + b^2 * z = b^3 := by
      have eq3 : x / b^3 - y / b^2 + z / b = 1 := h2'
      have eq4 : b ≠ 0 := h4 
      have eq5 : x / b^3 - y / b^2 + z / b = (x - b * y + b^2 * z) / b^3 := by 
        field_simp [h4]
        <;> ring 
      rw [eq5] at eq3 
      have eq6 : (x - b * y + b^2 * z) / b^3 = 1 := eq3 
      have eq7 : x - b * y + b^2 * z = b^3 := by
        field_simp [h4] at eq6 ⊢
        all_goals linarith 
      assumption 
    assumption
  
  have eq3 : x - c * y + c^2 * z = c^3 := by 
    have h3' : x / c^3 - y / c^2 + z / c = 1 := h3
    -- Multiply through by c^3 to clear denominators
    have h4 : c ≠ 0 := hc2
    have eq3'2 : x - c * y + c^2 * z = c^3 := by
      have eq3 : x / c^3 - y / c^2 + z / c = 1 := h3'
      have eq4 : c ≠ 0 := h4 
      have eq5 : x / c^3 - y / c^2 + z / c = (x - c * y + c^2 * z) / c^3 := by 
        field_simp [h4]
        <;> ring 
      rw [eq5] at eq3 
      have eq6 : (x - c * y + c^2 * z) / c^3 = 1 := eq3 
      have eq7 : x - c * y + c^2 * z = c^3 := by
        field_simp [h4] at eq6 ⊢
        all_goals linarith 
      assumption 
    assumption
  
  -- From eq1, eq2, eq3. Now solve the system
  have eq4 : -y + (a + b) * z = a^2 + a * b + b^2 := by
    have eq5 : (a - b) * y + (b^2 - a^2) * z = b^3 - a^3 := by
      nlinarith 
    have h4 : b^2 - a^2 = (b + a) * (b - a) := by ring
    have h5 : b^3 - a^3 = (b - a) * (b^2 + a * b + a^2) := by ring
    rw [h4, h5] at eq5
    have h6 : b - a ≠ 0 := by
      intro h8
      have : a = b := by linarith
      tauto 
    have : -y + (a + b) * z = a^2 + a * b + b^2 := by
      apply (mul_left_inj' h6).mp
      linarith 
    linarith
  
  have eq5 : -y + (a + c) * z = a^2 + a * c + c^2 := by 
    have eq6 : (a - c) * y + (c^2 - a^2) * z = c^3 - a^3 := by
      nlinarith 
    have h6 : c^2 - a^2 = (c + a) * (c - a) := by ring
    have h7 : c^3 - a^3 = (c - a) * (c^2 + a * c + a^2) := by ring
    rw [h6, h7] at eq6
    have h8 : c - a ≠ 0 := by
      intro h9
      have : a = c := by linarith
      tauto 
    have : -y + (a + c) * z = a^2 + a * c + c^2 := by
      apply (mul_left_inj' h8).mp
      linarith 
    linarith 

  -- Now solve for z
  have eq7 : z = a + b + c := by
    have eq8 : (b - c) * z = (a + b + c) * (b - c) := by
      nlinarith [eq4, eq5]
    have h4 : b - c ≠ 0 := by
      intro h
      apply hc
      linarith
    have : z = a + b + c := by
      apply (mul_left_inj' h4).mp
      linarith 
    assumption

  have eq8 : y = a * b + b * c + c * a := by
    rw [eq7] at eq4 
    nlinarith

  -- Finally solve for x
  have eq9 : x = a * b * c := by
    rw [eq8, eq7] at eq1
    nlinarith

  constructor 
  · exact eq9 
  constructor 
  · exact eq8 
  · exact eq7 
  all_goals nlinarith