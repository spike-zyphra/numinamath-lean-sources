import Mathlib

theorem algebra_210239 (k m n : ℝ) (h : ∃ x y, y = k * x + m ∧ y = m * x + n ∧ y = n * x + k) :
    k = m ∧ m = n := by
  rcases h with ⟨x, y, h1, h2, h3⟩
  have eq1 : k * x + m = m * x + n := by linarith
  have eq2 : k * x + m = n * x + k := by linarith
  have eq3 : m * x + n = n * x + k := by linarith
  -- Simplify the equations
  have eq1a : x * (k - m) = n - m := by
    linarith
    -- Rearrange to get the terms from different combinations to be 0.
  have eq2a : x * (k - n) = k - m := by
    linarith
  have eq3a : x * (m - n) = k - n := by
    linarith
  have eq4 : k - m = 0 := by
    nlinarith [sq_nonneg (k - m), sq_nonneg (k - n), sq_nonneg (m - n), sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x * (k - m) - (n - m)), sq_nonneg (x * (k - n) - (k - m)), sq_nonneg (x * (m - n) - (k - n))]
  have hkm : k = m := by linarith
  have hnm : n = m := by
    rw [show k - m = 0 by linarith] at eq1a
    have eq1b : n - m = 0 := by 
      nlinarith 
    linarith
  exact ⟨by linarith, by linarith⟩