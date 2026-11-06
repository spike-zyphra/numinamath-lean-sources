import Mathlib

theorem algebra_304922 (a : ℤ) (ha : 0 ≤ a) (x : ℤ)
    (h : a^2 * x^2 - (3 * a^2 - 8 * a) * x + 2 * a^2 - 13 * a + 15 = 0) :
    a = 1 ∨ a = 3 ∨ a = 5 := by 
  have h1 : (a * x - (2 * a - 3)) * (a * x - (a - 5)) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- First case where $a * x - (2 * a - 3) = 0$.
    have h4 : a * x = 2 * a - 3 := by
      linarith
    -- Rewrite to $a * (x - 2) = -3$.
    have h5 : a * (x - 2) = -3 := by
      linarith
    -- To show $a$ divides 3.
    have h6 : a ∣ 3 := by
      use -(x - 2)
      linarith
    -- Now a divides 3. So $a=1,3$.
    have h7 : a = 1 ∨ a = 3 := by
      have h8 : a ≤ 3 := by 
        apply Int.le_of_dvd (by omega) h6
      have h9 : a ≥ 0 := ha
      interval_cases a <;> omega
    rcases h7 with (ha1 | ha2)
    · -- a = 1
      left
      exact ha1
    · -- a = 3
      right
      left
      exact ha2
  · -- Second case where $a * x - (a - 5) = 0$.
    have h8 : a * x = a - 5 := by
      linarith
    -- Rewrite to $a * (x -1) = -5$.
    have h9 : a * (x - 1) = -5 := by
      linarith
    -- To show $a$ divides 5.
    have h10 : a ∣ 5 := by
      use -(x - 1)
      linarith
    -- Now a divides 5. So $a=1,5$.
    have h11 : a = 1 ∨ a = 5 := by 
      have h12 : a ≤ 5 := by 
        apply Int.le_of_dvd (by omega) h10
      have h13 : a ≥ 0 := ha
      interval_cases a <;> omega
    rcases h11 with (ha1 | ha5)
    · -- a = 1
      left
      exact ha1
    · -- a = 5
      right
      right
      exact ha5