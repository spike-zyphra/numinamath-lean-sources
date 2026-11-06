import Mathlib


theorem algebra_208436 (a : ℝ) (B : Set ℝ) (hB : B = {x | x^2 + 2 * (a + 1) * x + a^2 - 1 = 0}) (A : Set ℝ)
    (hA : A = {x | x^2 + 4 * x = 0}) (hBA : B ⊆ A) :
    a ≤ -1 ∨ a = 1 := by
  by_cases h1 : a ≤ -1
  · left
    exact h1
  · -- a > -1
    right
    have h2 : a > -1 := by linarith
    have h30 : (Real.sqrt (2 * a + 2)) ^ 2 = 2 * a + 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    have h10 : (- (a + 1) + Real.sqrt (2 * a + 2)) ^ 2 + 2 * (a + 1) * (- (a + 1) + Real.sqrt (2 * a + 2)) + a ^ 2 - 1 = 0 := by
      nlinarith [Real.sqrt_nonneg (2 * a + 2), Real.sq_sqrt (show (2 * a + 2) ≥ 0 by nlinarith)]
    have h11 : (- (a + 1) - Real.sqrt (2 * a + 2)) ^ 2 + 2 * (a + 1) * (- (a + 1) - Real.sqrt (2 * a + 2)) + a ^ 2 - 1 = 0 := by
      nlinarith [Real.sqrt_nonneg (2 * a + 2), Real.sq_sqrt (show (2 * a + 2) ≥ 0 by nlinarith)]
    have h12 : (- (a + 1) + Real.sqrt (2 * a + 2)) ∈ B := by
      rw [hB]
      exact h10
    have h13 : (- (a + 1) - Real.sqrt (2 * a + 2)) ∈ B := by
      rw [hB]
      exact h11
    have h14 : (- (a + 1) + Real.sqrt (2 * a + 2)) ∈ A := hBA h12
    have h15 : (- (a + 1) - Real.sqrt (2 * a + 2)) ∈ A := hBA h13
    rw [hA] at h14 h15
    have h16 : ((- (a + 1) + Real.sqrt (2 * a + 2)) ^ 2 + 4 * (- (a + 1) + Real.sqrt (2 * a + 2)) = 0) := by
      simpa using h14
    have h17 : ((- (a + 1) - Real.sqrt (2 * a + 2)) ^ 2 + 4 * (- (a + 1) - Real.sqrt (2 * a + 2)) = 0) := by
      simpa using h15
    have h18 : (- (a + 1) + Real.sqrt (2 * a + 2) = 0 ∨ - (a + 1) + Real.sqrt (2 * a + 2) = -4) := by
      have h160 : ((- (a + 1) + Real.sqrt (2 * a + 2)) ) * ((- (a + 1) + Real.sqrt (2 * a + 2) + 4) ) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h160) with
      | inl h => 
        left
        linarith
      | inr h => 
        right
        linarith
    have h19 : (- (a + 1) - Real.sqrt (2 * a + 2) = 0 ∨ - (a + 1) - Real.sqrt (2 * a + 2) = -4) := by
      have h170 : ((- (a + 1) - Real.sqrt (2 * a + 2)) ) * ((- (a + 1) - Real.sqrt (2 * a + 2) + 4) ) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h170) with
      | inl h => 
        left
        linarith
      | inr h => 
        right
        linarith
    cases h18 with
    | inl h180 =>
      have h20 : Real.sqrt (2 * a + 2) = a + 1 := by
        nlinarith
      have h21 : 2 * a + 2 = (a + 1) ^ 2 := by
        calc
          2 * a + 2 = (Real.sqrt (2 * a + 2)) ^ 2 := by
            rw [Real.sq_sqrt]
            nlinarith
          _ = (a + 1) ^ 2 := by
            rw [h20]
      have h22 : a ^ 2 - 1 = 0 := by
        nlinarith
      have h23 : a = 1 ∨ a = -1 := by
        have h1 : a ^ 2 = 1 := by
          nlinarith
        have : a = 1 ∨ a = -1 := by
          rw [sq_eq_one_iff] at h1
          tauto
        tauto
      cases h23 with
      | inl h24 => 
        tauto
      | inr h25 => 
        nlinarith
    | inr h181 =>
      have h20 : Real.sqrt (2 * a + 2) = a - 3 := by
        nlinarith
      have h2100 : a - 3 ≥ 0 := by
        have h00 : Real.sqrt (2 * a + 2) ≥ 0 := Real.sqrt_nonneg (2 * a + 2)
        nlinarith [Real.sq_sqrt (show (2 * a + 2) ≥ 0 by nlinarith)]
      have h21 : 2 * a + 2 = (a - 3) ^ 2 := by
        calc
          2 * a + 2 = (Real.sqrt (2 * a + 2)) ^ 2 := by
            rw [Real.sq_sqrt]
            nlinarith
          _ = (a - 3) ^ 2 := by
            rw [h20]
      have h22 : a ^ 2 - 8 * a + 7 = 0 := by
        nlinarith
      have h23 : (a - 1) * (a - 7) = 0 := by
        nlinarith
      have h24 : a = 1 ∨ a = 7 := by
        cases (mul_eq_zero.1 h23) with
        | inl h0 => 
          left
          linarith
        | inr h1 => 
          right
          linarith
      cases h24 with
      | inl h240 => 
        nlinarith
      | inr h241 => 
        have h70 : a = 7 := h241
        rw [show a = 7 by linarith [h70]] at h19
        have h71 : Real.sqrt (2 * (7 : ℝ) + 2) = 4 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
        have h72 : (- (7 + 1 : ℝ) - Real.sqrt (2 * (7 : ℝ) + 2)) = -12 := by
          rw [h71]
          norm_num
        rw [h72] at h19
        norm_num at h19