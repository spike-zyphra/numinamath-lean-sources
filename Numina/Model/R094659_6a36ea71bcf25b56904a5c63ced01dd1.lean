import Mathlib

theorem algebra_184770 {x y : ℝ} (h1 : x * y * (x + y) = 30) (h2 : x ^ 3 + y ^ 3 = 35) :
    (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) := by
  have h3 : (x + y) ^ 3 = 125 := by 
    have h_id : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y * (x + y)) := by
      ring
    rw [h2, h1] at h_id
    linarith
  have h4 : x + y = 5 := by
    have h5 : (x + y) ^ 3 - 125 = 0 := by linarith
    have h6 : (x + y - 5) * ((x + y) ^ 2 + 5 * (x + y) + 25) = 0 := by
      nlinarith [sq_nonneg ((x + y) ^ 2 + 5 * (x + y) + 25), sq_nonneg ((x + y) + 5 / 2)]
    cases (mul_eq_zero.1 h6) with 
    | inl h => linarith
    | inr h => 
      nlinarith [sq_nonneg ((x + y) + 5 / 2)]
  have h5 : x * y = 6 := by 
    rw [show x + y = 5 by linarith [h4] ] at h1 
    nlinarith
  have hquadratic : (x - 2) * (x - 3) = 0 := by 
    have eq1 : y = 5 - x := by
      linarith [h4]
    rw [eq1] at h5
    nlinarith
  cases' (mul_eq_zero.1 hquadratic) with hx hx
  · -- Case x - 2 = 0 (so x = 2)
    left
    constructor
    · -- x = 2
      linarith 
    · -- y = 3
      nlinarith 
  · -- Case x - 3 = 0 (so x = 3)
    right
    constructor
    · -- x = 3
      linarith 
    · -- y = 2
      nlinarith
  all_goals nlinarith