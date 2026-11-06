import Mathlib

theorem algebra_4085 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 - 2 * x * y + 3 * y^2 = 81) :
    x^2 + y ≤ 125 := by
  have h1 : (x - y) ^ 2 + 2 * y ^ 2 = 81 := by
    nlinarith
  have h2 : y ≤ 6 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y)]
  have h3 : y > 0 := hy
  have h4 : (y = 1) ∨ (y = 2) ∨ (y = 3) ∨ (y = 4) ∨ (y = 5) ∨ (y = 6) := by
    omega
  rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4)
  · -- y = 1
    rw [h4] at h1
    have h5 : (x - 1) ^ 2 = 79 := by
      nlinarith
    have h6 : (x - 1 : ℤ) ≤ 8 := by nlinarith [sq_nonneg ((x - 1 : ℤ)), h5]
    have h7 : (x - 1 : ℤ) ≥ -8 := by nlinarith [sq_nonneg ((x - 1 : ℤ)), h5]
    interval_cases h8 : (x - 1 : ℤ) <;> omega
  · -- y = 2
    rw [h4] at h1
    have h8 : (x - 2) ^ 2 = 73 := by
      nlinarith
    have h9 : (x - 2 : ℤ) ≤ 8 := by nlinarith [sq_nonneg ((x - 2 : ℤ)), h8]
    have h10 : (x - 2 : ℤ) ≥ -8 := by nlinarith [sq_nonneg ((x - 2 : ℤ)), h8]
    interval_cases h11 : (x - 2 : ℤ) <;> omega
  · -- y = 3
    rw [h4] at h1
    have h12 : (x - 3) ^ 2 = 63 := by
      nlinarith
    have h13 : (x - 3 : ℤ) ≤ 7 := by nlinarith [sq_nonneg ((x - 3 : ℤ)), h12]
    have h14 : (x - 3 : ℤ) ≥ -7 := by nlinarith [sq_nonneg ((x - 3 : ℤ)), h12]
    interval_cases h15 : (x - 3 : ℤ) <;> omega
  · -- y = 4
    rw [h4] at h1
    have h16 : (x - 4) ^ 2 = 49 := by
      nlinarith
    have h18 : (x - 4 : ℤ) = 7 ∨ (x - 4 : ℤ) = -7 := by
      have h17 : (x - 4 : ℤ) ^ 2 = 49 := by
        nlinarith
      have : (x - 4 : ℤ) = 7 ∨ (x - 4 : ℤ) = -7 := by
        have h18 : (x - 4 : ℤ) ^ 2 - 49 = 0 := by nlinarith
        have h19 : ((x - 4 : ℤ) - 7) * ((x - 4 : ℤ) + 7) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h19) with h20 h21
        · left
          linarith
        · right
          linarith
      assumption
    cases h18 with
    | inl h19 =>
      have hx11 : x = 11 := by linarith
      nlinarith
    | inr h20 =>
      have hx0 : x = -3 := by linarith
      nlinarith
  · -- y = 5
    rw [h4] at h1
    have h22 : (x - 5) ^ 2 = 31 := by
      nlinarith
    have h23 : (x - 5 : ℤ) ≤ 5 := by nlinarith [sq_nonneg ((x - 5 : ℤ)), h22]
    have h24 : (x - 5 : ℤ) ≥ -5 := by nlinarith [sq_nonneg ((x - 5 : ℤ)), h22]
    interval_cases h25 : (x - 5 : ℤ) <;> omega
  · -- y = 6
    rw [h4] at h1
    have h26 : (x - 6) ^ 2 = 9 := by
      nlinarith
    have h28 : (x - 6 : ℤ) = 3 ∨ (x - 6 : ℤ) = -3 := by
      have h27 : (x - 6 : ℤ) ^ 2 = 9 := by
        nlinarith
      have : (x - 6 : ℤ) = 3 ∨ (x - 6 : ℤ) = -3 := by
        have h28 : (x - 6 : ℤ) ^ 2 - 9 = 0 := by nlinarith
        have h29 : ((x - 6 : ℤ) - 3) * ((x - 6 : ℤ) + 3) = 0 := by
          nlinarith
        cases' (mul_eq_zero.1 h29) with h30 h31
        · left
          linarith
        · right
          linarith
      assumption
    cases h28 with
    | inl h29 =>
      have hx9 : x = 9 := by linarith
      nlinarith
    | inr h30 =>
      have hx3 : x = 3 := by linarith
      nlinarith