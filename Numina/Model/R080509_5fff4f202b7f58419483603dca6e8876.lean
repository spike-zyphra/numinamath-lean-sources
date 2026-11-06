import Mathlib

theorem algebra_235776 {n m : ℕ} (hn : n > 0) (hm : m > 0)
    (hnm : n * 2 + m * 3 > 30 ∧ n * 2 + m * 3 < 70)
    (h : (n * 2 + m * 3) * (1 - 1 / 5 : ℚ) = (m * 2 + n * 3)) :
    n * 2 + m * 3 = 50 := by

  have h1 : (n * 2 + m * 3 : ℚ) * (4 / 5) = m * 2 + n * 3 := by
    linarith
  have h2 : 7 * (n : ℚ) = 2 * (m : ℚ) := by
    field_simp at h1 ⊢
    linarith
  have h3 : 7 * n = 2 * m := by 
    have h4 : (7 * (n : ℚ) = 2 * (m : ℚ)) := h2
    have h5 : 7 * n = 2 * m := by
      exact_mod_cast h4
    exact h5

  have h4 : n * 2 + m * 3 > 30 := hnm.1
  have h5 : n * 2 + m * 3 < 70 := hnm.2
  
  have h6 : n * 2 + m * 3 = 50 := by
    omega 
  exact h6