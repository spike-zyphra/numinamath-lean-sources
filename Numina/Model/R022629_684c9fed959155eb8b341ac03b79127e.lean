import Mathlib

open Real

theorem algebra_15014 {a : ℕ → ℝ}
    (ha : ∀ n > 1, a n = 1 / logb n 2002) :
    (∑ i ∈ Finset.Icc 2 5, a i) - (∑ i ∈ Finset.Icc 10 14, a i) = -1 := by

  have h1 : a 2 = 1 / logb 2 2002 := by apply ha 2; linarith
  have h2 : a 3 = 1 / logb 3 2002 := by apply ha 3; linarith
  have h3 : a 4 = 1 / logb 4 2002 := by apply ha 4; linarith
  have h4 : a 5 = 1 / logb 5 2002 := by apply ha 5; linarith
  have h10 : a 10 = 1 / logb 10 2002 := by apply ha 10; linarith
  have h11 : a 11 = 1 / logb 11 2002 := by apply ha 11; linarith
  have h12 : a 12 = 1 / logb 12 2002 := by apply ha 12; linarith
  have h13 : a 13 = 1 / logb 13 2002 := by apply ha 13; linarith
  have h14 : a 14 = 1 / logb 14 2002 := by apply ha 14; linarith

  have h5 : (∑ i ∈ Finset.Icc (2 : ℕ) 5, a i) = a 2 + a 3 + a 4 + a 5 := by
    simp [Finset.sum_Icc_succ_top, add_assoc]
  have h6 : (∑ i ∈ Finset.Icc (10 : ℕ) 14, a i) = a 10 + a 11 + a 12 + a 13 + a 14 := by
    simp [Finset.sum_Icc_succ_top, add_assoc]

  rw [h5, h6, h1, h2, h3, h4, h10, h11, h12, h13, h14]

  have h7 : logb (2 : ℝ) 2002 = log (2002 : ℝ) / log (2 : ℝ) := by
    field_simp [logb]
  have h8 : logb (3 : ℝ) 2002 = log (2002 : ℝ) / log (3 : ℝ) := by
    field_simp [logb]
  have h9 : logb (4 : ℝ) 2002 = log (2002 : ℝ) / log (4 : ℝ) := by
    field_simp [logb]
  have h10 : logb (5 : ℝ) 2002 = log (2002 : ℝ) / log (5 : ℝ) := by
    field_simp [logb]
  have h11 : logb (10 : ℝ) 2002 = log (2002 : ℝ) / log (10 : ℝ) := by
    field_simp [logb]
  have h12 : logb (11 : ℝ) 2002 = log (2002 : ℝ) / log (11 : ℝ) := by
    field_simp [logb]
  have h13 : logb (12 : ℝ) 2002 = log (2002 : ℝ) / log (12 : ℝ) := by
    field_simp [logb]
  have h14 : logb (13 : ℝ) 2002 = log (2002 : ℝ) / log (13 : ℝ) := by
    field_simp [logb]
  have h15 : logb (14 : ℝ) 2002 = log (2002 : ℝ) / log (14 : ℝ) := by
    field_simp [logb]

  rw [h7, h8, h9, h10, h11, h12, h13, h14, h15]

  have h2002 : log (2002 : ℝ) = log (2 : ℝ) + log (7 : ℝ) + log (11 : ℝ) + log (13 : ℝ) := by
    calc
      log (2002 : ℝ) = log (2 * 7 * 11 * 13 : ℝ) := by norm_num
      _ = log (2 * 7 * 11) + log (13 : ℝ) := by rw [log_mul (by norm_num) (by norm_num)]
      _ = log (2 * 7) + log (11 : ℝ) + log (13 : ℝ) := by rw [log_mul (by norm_num) (by norm_num)]
      _ = log (2 : ℝ) + log (7 : ℝ) + log (11 : ℝ) + log (13 : ℝ) := by
        rw [log_mul (by norm_num) (by norm_num)]

  field_simp [h2002, log_mul, show log (4 : ℝ) = 2 * log (2 : ℝ) by { rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; simp [log_pow] },
              show log (5 : ℝ) = log (5 : ℝ) by rfl,
              show log (10 : ℝ) = log (2 : ℝ) + log (5 : ℝ) by { rw [show (10 : ℝ) = 2 * 5 by norm_num]; simp [log_mul] },
              show log (12 : ℝ) = log (2 : ℝ) + log (2 : ℝ) + log (3 : ℝ) by { rw [show (12 : ℝ) = 2 * 2 * 3 by norm_num]; simp [log_mul] },
              show log (14 : ℝ) = log (2 : ℝ) + log (7 : ℝ) by { rw [show (14 : ℝ) = 2 * 7 by norm_num]; simp [log_mul] } ]
  ring_nf
  <;> norm_num [h2002, log_mul, show log (4 : ℝ) = 2 * log (2 : ℝ) by { rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; simp [log_pow] },
              show log (5 : ℝ) = log (5 : ℝ) by rfl,
              show log (10 : ℝ) = log (2 : ℝ) + log (5 : ℝ) by { rw [show (10 : ℝ) = 2 * 5 by norm_num]; simp [log_mul] },
              show log (12 : ℝ) = log (2 : ℝ) + log (2 : ℝ) + log (3 : ℝ) by { rw [show (12 : ℝ) = 2 * 2 * 3 by norm_num]; simp [log_mul] },
              show log (14 : ℝ) = log (2 : ℝ) + log (7 : ℝ) by { rw [show (14 : ℝ) = 2 * 7 by norm_num]; simp [log_mul] } ]