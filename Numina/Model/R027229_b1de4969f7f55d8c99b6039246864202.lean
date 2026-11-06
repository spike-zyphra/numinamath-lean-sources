import Mathlib

theorem algebra_97669 (x m n : ℝ) (hm : 0 < m) (hn : n < 0)
    (h : (x - m) ^ 2 - (x - n) ^ 2 = (m - n) ^ 2) :
    x = n ∧ n < 0 := by

  have h1 : (x - m) ^ 2 - (x - n) ^ 2 = (m - n) ^ 2 := h

  have eq1 : (x - m) ^ 2 - (x - n) ^ 2 = 2 * (n - m) * x + (m ^ 2 - n ^ 2) := by
    nlinarith

  have eq2 : (m - n) ^ 2 = m ^ 2 - 2 * m * n + n ^ 2 := by
    ring

  rw [eq1, eq2] at h1

  have h2 : 2 * (n - m) * x = 2 * n * (n - m) := by
    linarith

  have h3 : x = n := by
    have h5 : (2 * (n - m)) * (x - n) = 0 := by
      linarith
    have h4 : n - m ≠ 0 := by
      nlinarith [hm, hn]

    have h6 : x - n = 0 := by
      apply (mul_left_inj' (show (2 * (n - m)) ≠ 0 by
        have h7 : n - m ≠ 0 := h4
        have h8 : (2 : ℝ) ≠ 0 := by norm_num
        simp [h7, h8]
      )).mp
      linarith

    linarith

  constructor
  · exact h3
  · -- Show that n < 0
    exact_mod_cast hn