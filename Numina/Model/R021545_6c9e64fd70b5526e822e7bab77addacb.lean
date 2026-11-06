import Mathlib

theorem algebra_5489 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x^6 + z^3 - 15 * x^2 * z = 3 * x^2 * y^2 * z - (y^2 + 5)^3) :
    (x, y, z) = (3, 2, 9) := by
  have eq1 : (x^2 : ℤ) ^ 3 + (y^2 + 5 : ℤ) ^ 3 + (z : ℤ) ^ 3 - 3 * (x^2 : ℤ) * (y^2 + 5 : ℤ) * (z : ℤ) = 0 := by
    nlinarith
  have h1 : (x^2 : ℤ) = (y^2 + 5 : ℤ) := by
    nlinarith [sq_nonneg ( (x^2 : ℤ) - (y^2 + 5 : ℤ) ), sq_nonneg ( (x^2 : ℤ) - (z : ℤ) ), sq_nonneg ( (y^2 + 5 : ℤ) - (z : ℤ) ) ]
  have h2 : (x^2 : ℤ) = (z : ℤ) := by
    nlinarith [sq_nonneg ( (x^2 : ℤ) - (y^2 + 5 : ℤ) ), sq_nonneg ( (x^2 : ℤ) - (z : ℤ) ), sq_nonneg ( (y^2 + 5 : ℤ) - (z : ℤ) ) ]
  have h3 : z = x^2 := by
    nlinarith
  have h4 : (x : ℤ) ^ 2 = (y : ℤ) ^ 2 + 5 := by
    nlinarith
  have h5 : (x - y : ℤ) * (x + y : ℤ) = 5 := by
    nlinarith
  have h6 : (x - y : ℤ) = 1 := by
    have h2 : (x - y : ℤ) ∣ 5 := by
      use (x + y : ℤ)
      all_goals linarith
    have h3 : (x - y : ℤ) = 1 ∨ (x - y : ℤ) = 5 ∨ (x - y : ℤ) = -1 ∨ (x - y : ℤ) = -5 := by
      have h5 : (x - y : ℤ) ∣ 5 := h2
      have h7 : (x - y : ℤ) ≤ 5 := by
        apply Int.le_of_dvd (by norm_num) h5
      have h8 : (x - y : ℤ) ≥ -5 := by
        have h9 : -(x - y : ℤ) ∣ 5 := by 
          exact Int.neg_dvd.2 h5
        have h10 : -(x - y : ℤ) ≤ 5 := by
          apply Int.le_of_dvd (by norm_num) h9
        linarith
      interval_cases (x - y : ℤ) <;> try tauto
    rcases h3 with (h | h | h | h)
    · 
      have h7 : (x + y : ℤ) = 5 := by
        nlinarith
      have hx1 : x = 3 := by
        linarith
      have hy1 : y = 2 := by
        linarith
      -- This is consistent, so valid
      linarith
    · 
      have h7 : (x + y : ℤ) = 1 := by
        nlinarith
      have h8 : x + y > 2 := by
        linarith [show x > 0 by linarith, show y > 0 by linarith]
      linarith
    · 
      have h7 : (x + y : ℤ) = -5 := by
        nlinarith
      have h8 : x + y > 2 := by
        linarith [show x > 0 by linarith, show y > 0 by linarith]
      linarith
    · 
      have h7 : (x + y : ℤ) = -1 := by
        nlinarith
      have h8 : x + y > 2 := by
        linarith [show x > 0 by linarith, show y > 0 by linarith]
      linarith
  have h7 : (x + y : ℤ) = 5 := by
    nlinarith
  have hx1 : x = 3 := by
    linarith
  have hy1 : y = 2 := by
    linarith
  have h8 : z = 9 := by
    rw [show x = 3 by linarith [hx1]] at h3
    nlinarith
  exact Prod.ext hx1 (Prod.ext hy1 h8)