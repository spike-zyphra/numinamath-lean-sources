import Mathlib

theorem other_56990 (a : ℕ → ℝ) (ha1 : a 1 = 2021)
    (han : ∀ n ≥ 1, a (n + 1) = Real.sqrt (4 + a n)) :
    ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ a 5 = Real.sqrt ((m + Real.sqrt n) / 2) +
      Real.sqrt ((m - Real.sqrt n) / 2) ∧ 10 * m + n = 45 := by

  have ha2 : a 2 = Real.sqrt (4 + a 1) := han 1 (by norm_num)
  rw [ha1] at ha2
  have ha2' : a 2 = 45 := by
    rw [ha2]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  have ha3 : a 3 = Real.sqrt (4 + a 2) := han 2 (by norm_num)
  rw [ha2'] at ha3
  have ha3' : a 3 = 7 := by
    rw [ha3]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

  have ha4 : a 4 = Real.sqrt (4 + a 3) := han 3 (by norm_num)
  rw [ha3'] at ha4
  have ha4' : a 4 = Real.sqrt 11 := by
    rw [ha4]
    rw [show (4 + 7 : ℝ) = 11 by norm_num]

  have ha5 : a 5 = Real.sqrt (4 + a 4) := han 4 (by norm_num)
  rw [ha4'] at ha5
  -- So, a_5 = Real.sqrt (4 + Real.sqrt 11)
  use 4, 5
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · -- Show that $a_5 = Real.sqrt ((4 + Real.sqrt 5) / 2) + Real.sqrt ((4 - Real.sqrt 5) / 2)$
    have h5 : Real.sqrt (4 + Real.sqrt 11) = Real.sqrt ((4 + Real.sqrt 5) / 2) + Real.sqrt ((4 - Real.sqrt 5) / 2) := by
      have h1 : (Real.sqrt ((4 + Real.sqrt 5) / 2) + Real.sqrt ((4 - Real.sqrt 5) / 2)) ^ 2 = (Real.sqrt (4 + Real.sqrt 11) ) ^2 := by
        have h2 : (Real.sqrt ((4 + Real.sqrt 5) / 2) + Real.sqrt ((4 - Real.sqrt 5) / 2)) ^ 2 =
            (Real.sqrt ((4 + Real.sqrt 5) / 2) )^2 +
              (Real.sqrt ((4 - Real.sqrt 5) / 2) )^2 +
                2 * (Real.sqrt ((4 + Real.sqrt 5) / 2) * Real.sqrt ((4 - Real.sqrt 5) / 2) ) := by ring
        have h3 : (Real.sqrt ((4 + Real.sqrt 5) / 2) )^2 = (4 + Real.sqrt 5) / 2 := Real.sq_sqrt (by
          have h61 : (0 : ℝ) ≤ (4 + Real.sqrt 5) / 2 := by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
          linarith
        )
        have h4 : (Real.sqrt ((4 - Real.sqrt 5) / 2) )^2 = (4 - Real.sqrt 5) / 2 := Real.sq_sqrt (by
          have h61 : (0 : ℝ) ≤ (4 - Real.sqrt 5) / 2 := by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
          linarith
        )
        have h51 : Real.sqrt ((4 + Real.sqrt 5) / 2) * Real.sqrt ((4 - Real.sqrt 5) / 2) = Real.sqrt 11 / 2 := by
          have h6 : Real.sqrt ((4 + Real.sqrt 5) / 2) * Real.sqrt ((4 - Real.sqrt 5) / 2) =
            Real.sqrt (( (4 + Real.sqrt 5) / 2 ) * ( (4 - Real.sqrt 5) / 2 ) ) := by
            rw [← Real.sqrt_mul (by
              have h61 : (0 : ℝ) ≤ (4 + Real.sqrt 5) / 2 := by
                nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
              have h62 : (0 : ℝ) ≤ (4 - Real.sqrt 5) / 2 := by
                nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
              nlinarith
            )]
          rw [h6]
          have h7 : ( (4 + Real.sqrt 5) / 2 ) * ( (4 - Real.sqrt 5) / 2 ) = (11 : ℝ) / 4 := by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
          rw [h7]
          have h8 : Real.sqrt ((11 : ℝ) / 4) = Real.sqrt 11 / 2 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            <;> ring_nf <;> norm_num
          linarith [h8]
        rw [h2, h3, h4, h51]
        have h6 : (Real.sqrt (4 + Real.sqrt 11)) ^ 2 = (4 + Real.sqrt 11) := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 11, Real.sqrt_nonneg ( (4 + Real.sqrt 5) / 2 ), Real.sqrt_nonneg ( (4 - Real.sqrt 5) / 2 ), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), h6]
      have h5_pos1 : 0 ≤ Real.sqrt (4 + Real.sqrt 11) := by positivity
      have h5_pos2 : 0 ≤ Real.sqrt ((4 + Real.sqrt 5) / 2) + Real.sqrt ((4 - Real.sqrt 5) / 2) := by
        positivity
      nlinarith [Real.sqrt_nonneg (4 + Real.sqrt 11), Real.sqrt_nonneg 5, Real.sqrt_nonneg ( (4 + Real.sqrt 5) / 2 ), Real.sqrt_nonneg ( (4 - Real.sqrt 5) / 2 ), h1, h5_pos1, h5_pos2, Real.sqrt_nonneg 5]
    rw [ha5]
    rw [h5]
    all_goals ring_nf <;> norm_num
    all_goals nlinarith [Real.sqrt_nonneg 11, Real.sqrt_nonneg 5, Real.sqrt_nonneg ( (4 + Real.sqrt 5) / 2 ), Real.sqrt_nonneg ( (4 - Real.sqrt 5) / 2 ), Real.sq_sqrt (show (11 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  · norm_num