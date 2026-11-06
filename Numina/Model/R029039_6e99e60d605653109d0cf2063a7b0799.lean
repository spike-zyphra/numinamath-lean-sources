import Mathlib


theorem algebra_603092 (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (han : ∀ n, a (n + 1) = a n + 1 / a n) :
    a 99 > 14 := by

  have ha1 : ∀ (n : ℕ), a n > 0 := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      all_goals norm_num
    | succ n ih =>
      have h5 : a (n + 1) = a n + 1 / a n := han n
      rw [h5]
      apply add_pos
      linarith [ih]
      apply div_pos
      norm_num
      linarith [ih]

  have h1 : ∀ (n : ℕ), a n ^ 2 ≥ (2 * (n : ℝ) + 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      norm_num
    | succ n ih =>
      have h2 : a (n + 1) = a n + 1 / a n := han n
      have h4 : a (n + 1) ^ 2 ≥ (2 * ((n + 1 : ℕ) : ℝ) + 1 : ℝ) := by
        rw [h2]
        have h6 : a n > 0 := by
          apply ha1 n
        have h7 : (a n + 1 / a n) ^ 2 = a n ^ 2 + 2 + (1 / (a n ^ 2 : ℝ)) := by
          field_simp
          <;> ring
        rw [h7]
        have h9 : (2 * ((n + 1 : ℕ) : ℝ) + 1 : ℝ) = (2 * (n : ℝ) + 1 + 2 : ℝ) := by
          simp at *
          <;> ring_nf
        rw [h9] at *
        have h10 : a n ^ 2 ≥ (2 * (n : ℝ) + 1 : ℝ) := by
          simpa using ih
        have h13 : (1 / (a n ^ 2 : ℝ)) > 0 := by
          apply div_pos
          norm_num
          nlinarith [ha1 n]
        nlinarith
      simpa using h4

  have h14 : a 99 ^ 2 ≥ (199 : ℝ) := by
    have h15 : a 99 ^ 2 ≥ (2 * ((99 : ℕ) : ℝ) + 1 : ℝ) := by
      apply h1 99
    norm_num at h15 ⊢
    linarith

  have h16 : a 99 > (0 : ℝ) := by
    apply ha1 99

  nlinarith [show (14 : ℝ) ^ 2 < a 99 ^ 2 by nlinarith]