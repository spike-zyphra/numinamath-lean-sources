import Mathlib

theorem algebra_95939 {x : ℝ} (hx : x > 3) :
    ¬(3 * x ^ 2 - 2 = 25) ∧ ¬((2 * x - 1) ^ 2 = (x - 1) ^ 2) ∧ ¬(Real.sqrt (x ^ 2 - 7) = Real.sqrt (x - 1)) := by 
  have h1 : ¬(3 * x ^ 2 - 2 = 25) := by
    intro h
    have h2 : x^2 = 9 := by linarith
    have h3 : x = 3 ∨ x = -3 := by
      have h4 : x^2 - 9 = 0 := by linarith
      have h5 : (x - 3) * (x + 3) = 0 := by nlinarith
      cases (mul_eq_zero.mp h5) with
      | inl h6 => 
          left
          linarith
      | inr h7 => 
          right
          nlinarith
    cases h3 with
    | inl h4 => 
      linarith -- x > 3 contradicts x = 3
    | inr h5 => 
      linarith -- x > 3 contradicts x = -3
  
  have h2 : ¬((2 * x - 1) ^ 2 = (x - 1) ^ 2) := by
    intro h
    have h3 : (2 * x - 1) ^ 2 - (x - 1) ^ 2 = 0 := by linarith
    have h4 : 3 * x^2 - 2 * x = 0 := by
      ring_nf at h3
      linarith
    have h5 : x * (3 * x - 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h5) with
    | inl h6 => 
      have h7 : x = 0 := by linarith
      linarith -- x > 3 contradicts x = 0
    | inr h8 => 
      have h9 : 3 * x - 2 = 0 := by linarith
      have h10 : x = 2 / 3 := by linarith
      linarith -- x > 3 contradicts x = 2/3
  
  have h3 : ¬(Real.sqrt (x ^ 2 - 7) = Real.sqrt (x - 1)) := by 
    intro h
    have h4 : Real.sqrt (x ^ 2 - 7) = Real.sqrt (x - 1) := h
  
    have h5 : x ^ 2 - 7 ≥ 0 := by
      by_contra h6
      push_neg at h6
      have h7 : Real.sqrt (x ^ 2 - 7) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      rw [h7] at h4
      have h8 : Real.sqrt (x - 1) = 0 := by 
        linarith
      have h9 : x - 1 ≥ 0 := by 
        by_contra h10
        push_neg at h10
        have h11 : Real.sqrt (x - 1) = 0 := by 
          rw [Real.sqrt_eq_zero']
          nlinarith
          all_goals nlinarith
        linarith [h8, h11]
      have h10 : x ≥ 1 := by linarith 
      have h11 : x ^ 2 - 7 ≥ 0 := by nlinarith [h6, h9]
      linarith -- contradiction
    have h6 : x - 1 ≥ 0 := by 
      by_contra h7
      push_neg at h7
      have h8 : Real.sqrt (x - 1) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      rw [h8] at h4
      have h9 : Real.sqrt (x ^ 2 - 7) = 0 := by 
        linarith
      have h10 : x ^ 2 - 7 ≥ 0 := by 
        by_contra h11
        push_neg at h11
        have h12 : Real.sqrt (x ^ 2 - 7) = 0 := by 
          rw [Real.sqrt_eq_zero']
          nlinarith
          all_goals nlinarith
        linarith [h9, h12]
      nlinarith
  
    have h7 : Real.sqrt (x ^ 2 - 7) ^ 2 = Real.sqrt (x - 1) ^ 2 := by 
      rw [h4]
  
    have h8 : Real.sqrt (x ^ 2 - 7) ^ 2 = x ^ 2 - 7 := Real.sq_sqrt (by nlinarith)
    have h9 : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (by nlinarith)
  
    have h10 : x^2 - 7 = x - 1 := by
      nlinarith
  
    have h11 : x^2 - x - 6 = 0 := by
      nlinarith
  
    have h12 : (x - 3) * (x + 2) = 0 := by
      nlinarith
  
    cases (mul_eq_zero.mp h12) with
    | inl h13 => 
      have h14 : x = 3 := by linarith 
      linarith -- x > 3 contradicts x = 3
    | inr h14 => 
      have h15 : x = -2 := by linarith 
      linarith -- x > 3 contradicts x = -2
  
  exact ⟨h1, h2, h3⟩