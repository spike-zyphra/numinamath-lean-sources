import Mathlib

theorem number_theory_222409 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / (a + b + c : ℝ) = 0.1 * a + 0.01 * b + 0.001 * c) :
    a = 1 ∧ b = 2 ∧ c = 5 := by
  have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by exact ha)
  have h2 : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by exact hb)
  have h3 : (c : ℝ) ≠ 0 := by exact_mod_cast (show c ≠ 0 by exact hc)
  have h4 : (a + b + c : ℝ) ≠ 0 := by
    by_contra h4
    have h5 : (a + b + c : ℝ) = 0 := by linarith
    have h6 : (1 / (a + b + c : ℝ) : ℝ) = 0 := by
      rw [h5]
      norm_num
    rw [h6] at h
    have h7 : (0.1 * a + 0.01 * b + 0.001 * c : ℝ) > 0 := by
      have ha1 : (a : ℝ) ≥ 1 := by
        have ha4 : a ≥ 1 := by
          by_contra h
          push_neg at h
          have : a = 0 := by linarith
          tauto
        exact_mod_cast ha4
      have hb1 : (b : ℝ) ≥ 1 := by
        have hb4 : b ≥ 1 := by
          by_contra h
          push_neg at h
          have : b = 0 := by linarith
          tauto
        exact_mod_cast hb4
      have hc1 : (c : ℝ) ≥ 1 := by
        have hc4 : c ≥ 1 := by
          by_contra h
          push_neg at h
          have : c = 0 := by linarith
          tauto
        exact_mod_cast hc4
      nlinarith [show (a : ℝ) ≥ 1 by linarith, show (b : ℝ) ≥ 1 by linarith, show (c : ℝ) ≥ 1 by linarith]
    linarith

  have h12 : 1 = (0.1 * a + 0.01 * b + 0.001 * c : ℝ) * (a + b + c : ℝ) := by 
    have h13 : (1 / (a + b + c : ℝ) : ℝ) = (0.1 * a + 0.01 * b + 0.001 * c : ℝ) := by
      linarith [h]
    have h14 : (a + b + c : ℝ) ≠ 0 := h4
    field_simp at h13 ⊢
    nlinarith
  
  have h15 : (1000 : ℝ) = (a + b + c : ℝ) * (100 * (a : ℝ) + 10 * (b : ℝ) + (c : ℝ)) := by
    ring_nf at h12 ⊢
    nlinarith
  
  have h16 : (1000 : ℤ) = (a + b + c : ℤ) * (100 * (a : ℤ) + 10 * (b : ℤ) + (c : ℤ)) := by
    have h17 : (1000 : ℝ) = (a + b + c : ℝ) * (100 * (a : ℝ) + 10 * (b : ℝ) + (c : ℝ)) := h15
    exact_mod_cast h17
  
  have h18 : a ≥ 1 := by omega
  have h19 : b ≥ 1 := by omega
  have h20 : c ≥ 1 := by omega

  have h21 : a ≤ 9 := by
    nlinarith [show (1000 : ℤ) = (a + b + c : ℤ) * (100 * (a : ℤ) + 10 * (b : ℤ) + (c : ℤ)) from by nlinarith, 
      show (a : ℤ) ≥ 1 by omega, show (b : ℤ) ≥ 1 by omega, show (c : ℤ) ≥ 1 by omega]

  have h22 : b ≤ 9 := by
    nlinarith [show (1000 : ℤ) = (a + b + c : ℤ) * (100 * (a : ℤ) + 10 * (b : ℤ) + (c : ℤ)) from by nlinarith, 
      show (a : ℤ) ≥ 1 by omega, show (b : ℤ) ≥ 1 by omega, show (c : ℤ) ≥ 1 by omega]

  have h23 : c ≤ 9 := by
    nlinarith [show (1000 : ℤ) = (a + b + c : ℤ) * (100 * (a : ℤ) + 10 * (b : ℤ) + (c : ℤ)) from by nlinarith, 
      show (a : ℤ) ≥ 1 by omega, show (b : ℤ) ≥ 1 by omega, show (c : ℤ) ≥ 1 by omega]

  interval_cases a <;> try { 
    omega 
  } <;> try { 
    interval_cases b <;> try { 
      omega 
    } <;> try { 
      interval_cases c 
      <;> omega 
    }
  }