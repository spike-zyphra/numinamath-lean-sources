import Mathlib

open Real

theorem algebra_234676 : ∑ i ∈ Finset.range 1010, sqrt (2 * i + 2 - sqrt ((2 * i + 1) * (2 * i + 3))) = (sqrt 2021 - 1) / sqrt 2 := by

  have h1 : ∀ i : ℕ, sqrt (2 * i + 2 - sqrt ((2 * i + 1) * (2 * i + 3))) = Real.sqrt ((2 * (i : ℝ) + 3) / 2) - Real.sqrt ((2 * (i : ℝ) + 1) / 2) := by
    intro i
    have h2 : (2 * i + 2 - sqrt ((2 * i + 1) * (2 * i + 3)) : ℝ) = (Real.sqrt ((2 * (i : ℝ) + 3) / 2) - Real.sqrt ((2 * (i : ℝ) + 1) / 2)) ^ 2 := by
      have h3 : Real.sqrt ((2 * (i : ℝ) + 3) / 2) ^ 2 = (2 * (i : ℝ) + 3) / 2 := by
        rw [Real.sq_sqrt]
        positivity
      have h4 : Real.sqrt ((2 * (i : ℝ) + 1) / 2) ^ 2 = (2 * (i : ℝ) + 1) / 2 := by
        rw [Real.sq_sqrt]
        positivity
      have h5 : Real.sqrt ((2 * (i : ℝ) + 3) / 2) * Real.sqrt ((2 * (i : ℝ) + 1) / 2) = Real.sqrt (((2 * (i : ℝ) + 3) / 2) * ((2 * (i : ℝ) + 1) / 2)) := by
        rw [← Real.sqrt_mul (by positivity)]
      have h6 : ((2 * (i : ℝ) + 3) / 2) * ((2 * (i : ℝ) + 1) / 2) = ((2 * i + 1 : ℝ) * (2 * i + 3)) / 4 := by
        ring_nf
      have h7 : Real.sqrt (((2 * (i : ℝ) + 3) / 2) * ((2 * (i : ℝ) + 1) / 2)) = (Real.sqrt ((2 * i + 1 : ℝ) * (2 * i + 3)) ) / 2 := by
        rw [h6]
        have h8 : Real.sqrt (((2 * i + 1 : ℝ) * (2 * i + 3)) / 4) = (Real.sqrt ((2 * i + 1 : ℝ) * (2 * i + 3)) ) / 2 := by
          have h9 : Real.sqrt (((2 * i + 1 : ℝ) * (2 * i + 3)) / 4) = Real.sqrt ((2 * i + 1 : ℝ) * (2 * i + 3)) / Real.sqrt (4 : ℝ) := by
            rw [Real.sqrt_div (by positivity)]
          have h10 : Real.sqrt (4 : ℝ) = 2 := by
            rw [Real.sqrt_eq_cases]
            norm_num
          rw [h9, h10]
        linarith [h8]
      nlinarith [Real.sqrt_nonneg ((2 * (i : ℝ) + 3) / 2), Real.sqrt_nonneg ((2 * (i : ℝ) + 1) / 2), sq_nonneg (Real.sqrt ((2 * (i : ℝ) + 3) / 2) - Real.sqrt ((2 * (i : ℝ) + 1) / 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * i + 1 : ℝ) * (2 * i + 3) by positivity)]
    have h8 : Real.sqrt ((2 * (i : ℝ) + 3) / 2) ≥ Real.sqrt ((2 * (i : ℝ) + 1) / 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h9 : Real.sqrt ((2 * i + 2 - sqrt ((2 * i + 1) * (2 * i + 3)) : ℝ)) = Real.sqrt ((Real.sqrt ((2 * (i : ℝ) + 3) / 2) - Real.sqrt ((2 * (i : ℝ) + 1) / 2)) ^ 2) := by
      rw [h2]
    have h10 : Real.sqrt ((Real.sqrt ((2 * (i : ℝ) + 3) / 2) - Real.sqrt ((2 * (i : ℝ) + 1) / 2)) ^ 2) = Real.sqrt ((2 * (i : ℝ) + 3) / 2) - Real.sqrt ((2 * (i : ℝ) + 1) / 2) := by
      apply Real.sqrt_sq
      linarith [Real.sqrt_nonneg ((2 * (i : ℝ) + 3) / 2), Real.sqrt_nonneg ((2 * (i : ℝ) + 1) / 2), h8]
    rw [h9, h10]

  rw [Finset.sum_congr rfl (fun i _ => h1 i)]

  have h3 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (Real.sqrt ((2 * (i : ℝ) + 3) / 2) - Real.sqrt ((2 * (i : ℝ) + 1) / 2)) = Real.sqrt ((2 * ((n : ℝ) ) + 1) / 2) - Real.sqrt ((1 : ℝ) / 2) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      ring_nf

  specialize h3 1010
  rw [h3]

  have h4 : Real.sqrt ((2 * ((1010 : ℕ) : ℝ) + 1) / 2) = Real.sqrt (2021 / 2 : ℝ) := by
    norm_num

  rw [h4]

  have h5 : Real.sqrt (2021 / 2 : ℝ) = Real.sqrt (2021 : ℝ) / Real.sqrt (2 : ℝ) := by
    rw [show (2021 / 2 : ℝ) = (2021 : ℝ) / (2 : ℝ) by norm_num]
    rw [Real.sqrt_div (by norm_num)]

  have h6 : Real.sqrt ((1 : ℝ) / 2) = (1 : ℝ) / Real.sqrt (2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (1 : ℝ) / (2 : ℝ) by norm_num]
    rw [Real.sqrt_div (by norm_num)]
    have h7 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by
      rw [Real.sqrt_one]
    rw [h7]

  rw [h5, h6]

  field_simp
  <;> ring