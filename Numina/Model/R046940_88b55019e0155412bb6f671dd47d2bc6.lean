import Mathlib

theorem algebra_14474 (x : ℝ) :
    (x^3 + 2 * x^2) / (x^2 + 3 * x + 2) + x = -6 ↔ x = -3 / 2 := by
  constructor
  · -- Assume the equation holds, prove x = -3/2
    intro h 
    by_cases h1 : x^2 + 3 * x + 2 = 0
    · -- The denominator is zero
      have h2 : (x + 1) * (x + 2) = 0 := by 
        linarith [h1]
      cases' (mul_eq_zero.mp h2) with h3 h4 
      · -- Case x + 1 = 0, so x = -1
        have h5 : x = -1 := by linarith 
        rw [h5] at h 
        norm_num at h 
      · -- Case x + 2 = 0, so x = -2 
        have h5 : x = -2 := by linarith 
        rw [h5] at h 
        norm_num at h 
    · -- The denominator is non-zero 
      have h1' : x^2 + 3 * x + 2 ≠ 0 := by 
        intro h_eq 
        apply h1 
        exact h_eq 
      have eq2 : (x^3 + 2 * x^2) / (x^2 + 3 * x + 2) + x = -6 := by linarith [h] 
      have eq3 : (x^3 + 2 * x^2) + x * (x^2 + 3 * x + 2) = -6 * (x^2 + 3 * x + 2) := by 
        field_simp [h1'] at eq2 
        nlinarith 
      have eq4 : 2 * x^3 + 11 * x^2 + 20 * x + 12 = 0 := by 
        nlinarith [eq3] 
      have eq5 : (x + 3 / 2) * (2 * (x + 2) ^ 2) = 0 := by 
        ring_nf at eq4 ⊢ 
        nlinarith 
      cases' (mul_eq_zero.mp eq5) with eq6 eq7 
      · -- Case x + 3/2 = 0 
        linarith 
      · -- Case 2 * (x + 2) ^ 2 = 0 
        have h5 : x = -2 := by 
          nlinarith 
        have h5' : x^2 + 3 * x + 2 = 0 := by 
          rw [h5] 
          norm_num 
        contradiction 
  · -- Assume x = -3/2, prove the equation 
    intro h 
    rw [h] 
    norm_num