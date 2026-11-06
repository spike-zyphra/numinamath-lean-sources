import Mathlib

theorem algebra_271397 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : (a + b - c) / c = (a - b + c) / b) (h2 : (a - b + c) / b = (-a + b + c) / a)
    (x : ℝ) (hx : x = ((a + b) * (b + c) * (c + a)) / (a * b * c)) (hx0 : x < 0) :
    x = -1 := by

  have eq1 : (a + b - c) * b = (a - b + c) * c := by 
    have h11 : (a + b - c) / c = (a - b + c) / b := h1
    field_simp [hc, hb] at h11 ⊢
    nlinarith
  
  have eq2 : (a - b + c) * a = (-a + b + c) * b := by 
    have h22 : (a - b + c) / b = (-a + b + c) / a := h2
    field_simp [hb, ha] at h22 ⊢
    nlinarith
  
  have eq3 : (b - c) * (a + b + c) = 0 := by
    nlinarith [eq1]

  have eq4 : (a - b) * (a + b + c) = 0 := by
    nlinarith [eq2]

  by_cases h : a + b + c = 0 
  · -- If a + b + c = 0, compute x.
    have hc2 : c = - (a + b) := by 
      linarith 
    have hx1 : x = -1 := by 
      rw [hx] 
      have hc22 : c = - (a + b) := hc2 
      have eq5 : (a + b) * (b + c) * (c + a) = a * b * (a + b) := by 
        rw [show c = - (a + b) by linarith [hc22]]
        ring_nf 
      have eq6 : a * b * c = - (a * b * (a + b)) := by 
        rw [show c = - (a + b) by linarith [hc22]]
        ring 
      rw [eq5, eq6] 
      have h7 : a + b ≠ 0 := by 
        by_contra h7 
        have h8 : c = 0 := by 
          linarith [hc22, h7] 
        contradiction 
      have h8 : a * b * (a + b) ≠ 0 := by 
        apply mul_ne_zero 
        apply mul_ne_zero 
        · exact ha 
        · exact hb 
        · exact h7 
      field_simp [(show a * b * (a + b) ≠ 0 by assumption )] 
      <;> ring
    linarith [hx1]
  
  · -- If a + b + c ≠ 0, derive a contradiction.
    -- If a + b + c ≠ 0, derive a contradiction.
    have hne : a + b + c ≠ 0 := h

    have heq1 : b - c = 0 := by
      apply_fun (fun y => y / (a + b + c)) at eq3
      field_simp [show a + b + c ≠ 0 by assumption] at eq3 
      linarith

    have heq2 : a - b = 0 := by 
      apply_fun (fun y => y / (a + b + c)) at eq4
      field_simp [show a + b + c ≠ 0 by assumption] at eq4
      linarith

    have heq3 : a = b := by linarith
  
    have heq4 : b = c := by linarith

    -- Thus a = b = c
  
    have ha2 : a * b * c = a ^ 3 := by 
      have hb2 : b = a := by linarith 
      have hc2 : c = a := by linarith 
      rw [hb2, hc2] 
      ring
  
    have hx2 : x = 8 := by 
      rw [hx] 
      have h5 : (a + b) * (b + c) * (c + a) = 8 * (a ^ 3) := by 
        have hb2 : b = a := by linarith 
        have hc2 : c = a := by linarith 
        rw [hb2, hc2] 
        ring 
      rw [h5, ha2] 
      have : a ≠ 0 := ha 
      field_simp [show a ≠ 0 by assumption]
      <;> ring
  
    linarith