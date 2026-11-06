import Mathlib

open Real

theorem inequalities_126252 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c) / 3 ≤ sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) ∧
    ((a + b + c) / 3 = sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) ↔
      (a = b ∧ b = c)) := by
  have h1 : (a + b + c) / 3 ≤ sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) := by
    have h2 : ((a + b + c) / 3) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h3 : ((a + b + c) / 3) ≥ 0 := by 
      nlinarith
    have h4 : sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) ≥ 0 := by positivity
    have h5 : ((a + b + c) / 3) ≤ Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) := by
      apply Real.le_sqrt_of_sq_le 
      linarith [h2]
    exact h5
  have h2 : ((a + b + c) / 3 = sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) ↔
    (a = b ∧ b = c)) := by
    constructor
    · -- Forward direction: Equality implies a = b = c
      intro heq
      have h_eq1 : ((a + b + c) / 3) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by
        have h1 : ((a + b + c) / 3) = Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) := by linarith [heq]
        have h2 : (Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3)) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by
          rw [Real.sq_sqrt]
          nlinarith [show 0 ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 3 by positivity]
        nlinarith [h1, h2]
      have h_eq2 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
        nlinarith [h_eq1]
      have hab : (a - b) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have hbc : (b - c) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have ha_eq : a = b := by nlinarith [hab]
      have hb_eq : b = c := by nlinarith [hbc]
      exact ⟨ha_eq, hb_eq⟩
    · -- Backward direction: a = b = c implies equality
      rintro ⟨rfl, rfl⟩
      have ha2 : 0 ≤ a := by linarith
      have h_eq : Real.sqrt ((a ^ 2 + a ^ 2 + a ^ 2) / 3) = a := by
        have h1 : (a ^ 2 + a ^ 2 + a ^ 2) / 3 = a ^ 2 := by
          nlinarith
        rw [h1]
        rw [Real.sqrt_sq]
        linarith
      have h2 : (a + a + a) / 3 = a := by
        nlinarith
      linarith [h_eq, h2]
  constructor
  · exact h1
  · exact h2