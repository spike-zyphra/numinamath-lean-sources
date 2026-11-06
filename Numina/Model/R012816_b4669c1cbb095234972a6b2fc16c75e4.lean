import Mathlib

theorem number_theory_3891 (x : ℤ) (hx : x > 0) :
    ¬ ∃ m, m^2 = x * (x + 1) * (x + 2) * (x + 3) := by
  rintro ⟨m, hm⟩
  have h1 : x * (x + 1) * (x + 2) * (x + 3) = (x^2 + 3 * x) ^ 2 + 2 * (x^2 + 3 * x) := by
    ring
  have h3 : m^2 = (x^2 + 3 * x) ^ 2 + 2 * (x^2 + 3 * x) := by 
    rw [h1] at hm 
    linarith
  have h4 : m ^ 2 > (x^2 + 3 * x) ^ 2 := by
    nlinarith [h3, sq_pos_of_pos (show x > 0 by linarith)]
  have h5 : m ^ 2 < (x^2 + 3 * x + 1) ^ 2 := by
    nlinarith [h3, sq_pos_of_pos (show x > 0 by linarith)]
  have h6 : m > (x^2 + 3 * x) ∨ m < - (x^2 + 3 * x) := by 
    by_contra h
    push_neg at h
    have h7 : m ≤ x^2 + 3 * x := by nlinarith
    have h8 : m ≥ - (x^2 + 3 * x) := by nlinarith
    have h9 : m ^ 2 ≤ (x^2 + 3 * x) ^ 2 := by
      nlinarith [sq_nonneg (m + (x^2 + 3 * x)), sq_nonneg (m - (x^2 + 3 * x)), sq_nonneg (m), sq_nonneg (x^2 + 3 * x), mul_pos (show 0 < (x: ℤ) by linarith) (show 0 < (x: ℤ) by linarith)]
    nlinarith
  rcases h6 with (h6 | h6)
  · -- Case where $m > x^2 + 3x$.
    exfalso
    have h8 : m ≥ x^2 + 3 * x + 1 := by omega
    have h9 : m ^ 2 ≥ (x^2 + 3 * x + 1) ^ 2 := by nlinarith [h8, sq_nonneg (m - (x^2 + 3 * x + 1)), sq_nonneg (m), sq_nonneg (x^2 + 3 * x + 1)]
    nlinarith
  · -- Case where $m < - (x^2 + 3x)$.
    exfalso
    have h8 : m ≤ - (x^2 + 3 * x) - 1 := by omega
    have h9 : m ^ 2 ≥ (x^2 + 3 * x + 1) ^ 2 := by 
      nlinarith [sq_nonneg (m + (x^2 + 3 * x + 1)), sq_nonneg (m - ( - (x^2 + 3 * x) - 1)), sq_nonneg (m), sq_nonneg (x^2 + 3 * x + 1), mul_pos (show 0 < (x: ℤ) by linarith) (show 0 < (x: ℤ) by linarith)]
    nlinarith