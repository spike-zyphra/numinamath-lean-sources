import Mathlib

theorem algebra_265138 (a : ℕ → ℤ) (h0 : 0 < a 0) (h1 : a 0 < a 1)
    (h2 : a 1 < a 2) (h3 : a 2 < a 3)
    (h_arith : a 0 + a 2 = 2 * a 1) (h_geo : a 1 * a 3 = a 2 ^ 2)
    (h_sub : a 3 - a 0 = 30) :
    a 0 + a 1 + a 2 + a 3 = 129 := by 

  have ha2 : a 2 = 2 * a 1 - a 0 := by 
    omega 
  have ha3 : a 3 = a 0 + 30 := by 
    omega 

  rw [ha3, ha2] at h_geo
  have h5 : a 1 * (a 0 + 30) = (2 * a 1 - a 0) ^ 2 := by 
    linarith

  have h7 : a 1 < a 0 + 15 := by -- First, let's find a tighter upper bound for a 1
    have h8 : a 2 < a 3 := by linarith [h3]
    rw [ha2, ha3] at h8 
    nlinarith

  have h6 : a 0 = 18 := by
    have h5' : a 1 * (a 0 + 30) = (2 * a 1 - a 0) ^ 2 := h5

    have ha0 : a 0 > 0 := by
      linarith [h0]
    have ha1 : a 1 > 0 := by
      nlinarith [h0, h1]
    have ha5 : a 0 < a 1 := by linarith [h1]
    have k_eq : a 1 - a 0 ≥ 1 := by
      omega 
    have k_le : a 1 - a 0 ≤ 14 := by 
      omega 
    interval_cases h8 : a 1 - a 0 <;> try { 
      omega 
    } <;> try { 
      rw [show a 1 = a 0 + 1 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 2 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 3 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 4 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 5 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 6 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 7 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 8 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 9 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 10 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 11 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 12 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 13 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    } <;> try { 
      rw [show a 1 = a 0 + 14 by omega] at h5' 
      ring_nf at h5' 
      have h0' : a 0 > 0 := by linarith 
      have : a 0 ≤ 30 := by nlinarith 
      interval_cases h9 : a 0 <;> omega 
    }
  have h8 : a 1 = 27 := by
    rw [show a 0 = 18 by linarith [h6]] at h5 
    nlinarith
  have ha2' : a 2 = 36 := by 
    rw [show a 1 = 27 by linarith [h8], show a 0 = 18 by linarith [h6]] at ha2
    omega
  have ha3' : a 3 = 48 := by 
    rw [show a 0 = 18 by linarith [h6]] at ha3 
    omega 
  linarith [h6, h8, ha2', ha3']