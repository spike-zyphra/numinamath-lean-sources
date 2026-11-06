import Mathlib

theorem algebra_13340 : Complex.I^11 + Complex.I^111 = -2 * Complex.I := by 
  have h1 : Complex.I ^ 11 = -Complex.I := by 
    have h : Complex.I ^ 3 = -Complex.I := by
      calc 
        Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
        _ = (-1) * Complex.I := by simp [Complex.I_sq]
        _ = -Complex.I := by ring 
    calc 
      Complex.I ^ 11 = Complex.I ^ 3 * (Complex.I ^ 8) := by ring 
      _ = Complex.I ^ 3 * 1 := by 
        have h2 : Complex.I ^ 8 = 1 := by 
          calc 
            Complex.I ^ 8 = (Complex.I ^ 4) ^ 2 := by ring 
            _ = (1) ^ 2 := by simp [Complex.I_sq] 
            _ = 1 := by ring 
        rw [h2] 
      _ = -Complex.I * 1 := by rw [h] 
      _ = -Complex.I := by ring 
  have h2 : Complex.I ^ 111 = -Complex.I := by 
    have h3 : Complex.I ^ 3 = -Complex.I := by
      calc 
        Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring 
        _ = (-1) * Complex.I := by simp [Complex.I_sq] 
        _ = -Complex.I := by ring 
      -- h3 : Complex.I ^ 3 = -Complex.I
    calc 
      Complex.I ^ 111 = Complex.I ^ 3 * (Complex.I ^ 108) := by ring 
      _ = Complex.I ^ 3 * 1 := by 
        have h4 : Complex.I ^ 108 = 1 := by 
          calc 
            Complex.I ^ 108 = (Complex.I ^ 4) ^ 27 := by ring 
            _ = (1) ^ 27 := by simp [Complex.I_sq] 
            _ = 1 := by norm_num 
        rw [h4] 
      _ = -Complex.I * 1 := by rw [h3] 
      _ = -Complex.I := by ring 
  rw [h1, h2] 
  ring 
  all_goals norm_num 
  <;> norm_num 
  <;> try tauto 
  <;> try linarith 
  <;> try { 
    apply Complex.ext 
    all_goals norm_num 
  } 
  <;> try { 
    ring_nf 
    <;> norm_num 
  } 
  all_goals try { 
    tauto 
    <;> try { 
      tauto 
      <;> norm_num 
    } 
  }