import Mathlib

theorem algebra_1159
    {a b c : ℚ}
    (ha : a + b ≠ 0)
    (hb : b + c ≠ 0)
    (hc : a + c ≠ 0)
    (h1 : a * b / (a + b) = 1 / 3)
    (h2 : b * c / (b + c) = 1 / 7)
    (h3 : a * c / (a + c) = 1 / 12) :
    a * b * c / (a * b + b * c + a * c) = 1 / 11 := by

  have eq1 : 3 * (a * b) = a + b := by 
    have h1' : a + b ≠ 0 := ha
    field_simp [h1'] at h1 ⊢
    linarith

  have eq2 : 7 * (b * c) = b + c := by 
    have h2' : b + c ≠ 0 := hb
    field_simp [h2'] at h2 ⊢
    linarith

  have eq3 : 12 * (a * c) = a + c := by 
    have h3' : a + c ≠ 0 := hc
    field_simp [h3'] at h3 ⊢
    linarith

  have ha0 : a ≠ 0 := by
    by_contra h
    have ha' : a = 0 := by linarith
    rw [ha'] at eq1 eq3
    have h1' : b = 0 := by 
      nlinarith
    have h1_zero : a + b = 0 := by
      linarith [ha', h1']
    contradiction

  have hb0 : b ≠ 0 := by 
    by_contra h
    have hb' : b = 0 := by linarith
    rw [hb'] at eq1 eq2
    have h1_zero : a + b = 0 := by 
      nlinarith [hb']
    contradiction

  have hc0 : c ≠ 0 := by 
    by_contra h
    have hc' : c = 0 := by linarith
    rw [hc'] at eq2 eq3
    have h1_zero : a + c = 0 := by 
      nlinarith [hc']
    contradiction
  
  have l1 : 3 * a * b - a - b = 0 := by 
    linarith [eq1]
  
  have l2 : 7 * b * c - b - c = 0 := by 
    linarith [eq2]

  have l3 : 12 * a * c - a - c = 0 := by 
    linarith [eq3]

  have eq7 : 4 * a * c - a + c = 0 := by
    have eq8 : 7 * a * b * c - a * b - a * c = 0 := by
      have eq2' : 7 * (b * c) = b + c := eq2
      have eq2'' : 7 * b * c - b - c = 0 := by linarith [eq2']
      calc
        7 * a * b * c - a * b - a * c = a * (7 * b * c - b - c) := by ring
        _ = a * 0 := by rw [eq2'']
        _ = (0 : ℚ) := by ring

    have eq9 : 3 * a * b * c - a * c - b * c = 0 := by
      have eq1' : 3 * (a * b) = a + b := eq1
      have eq1'' : 3 * a * b - a - b = 0 := by linarith [eq1']
      calc 
        3 * a * b * c - a * c - b * c = c * (3 * a * b - a - b) := by ring 
        _ = c * 0 := by rw [eq1'']
        _ = (0 : ℚ) := by ring
    have eq10 : 4 * a * b * c - a * b + b * c = 0 := by
      nlinarith [eq8, eq9]
    have eq11 : b * (4 * a * c - a + c) = 0 := by
      linarith [eq10]
    cases' (mul_eq_zero.1 eq11) with eq12 eq13 
    · -- eq12 : b = 0 is impossible
      exfalso 
      apply hb0 
      linarith 
    · -- eq13 : 4*a*c -a +c =0 
      linarith [eq13]

  have eq8 : c = 1 / 8 := by
    have eq6' : 8 * a * c - a = 0 := by
      nlinarith 
    have eq9 : a ≠ 0 := ha0 
    have : 8 * c = 1 := by
      apply (mul_left_inj' eq9).mp
      linarith 
    linarith

  have eq9 : a = 1 / 4 := by
    rw [eq8] at l3 
    nlinarith 
    all_goals linarith
  
  have eq10 : b = -1 := by 
    rw [eq9] at l1 
    nlinarith
  
  have h_eq : a * b * c = -1 / 32 := by
    rw [eq9, eq10, eq8] 
    norm_num

  have h_eq2 : a * b + b * c + a * c = -11 / 32 := by
    rw [eq9, eq10, eq8] 
    norm_num
  
  rw [h_eq, h_eq2] 
  all_goals norm_num
  all_goals tauto