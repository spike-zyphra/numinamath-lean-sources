import Mathlib

open Complex Polynomial Real

theorem algebra_249769 : ∑ k ∈ Finset.range 2013, (k + 1) * I ^ (k + 1) = 1006 + 1007 * I := by

  have h3 : ∀ (n : ℕ), ∑ k ∈ Finset.range (4 * n + 1), (k + 1) * I ^ (k + 1) =
          2 * n + (2 * n + 1) * I := by
    intro n
    induction n with
    | zero =>
      norm_num [Finset.sum_range_succ, pow_succ, Complex.ext_iff, mul_add, mul_assoc, Complex.I_mul_I]
    | succ n ih =>
      rw [show 4 * (n + 1) + 1 = 4 * n + 1 + 4 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h30 : I ^ (4 * n + 2) = -1 := by
        have h7 : I ^ 4 = 1 := by
          norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
        calc
          I ^ (4 * n + 2) = (I ^ 4) ^ n * I ^ 2 := by ring
          _ = (1) ^ n * I ^ 2 := by rw [h7]
          _ = I ^ 2 := by ring
          _ = -1 := by
            simp [Complex.I_sq]
      have h31 : I ^ (4 * n + 3) = -I := by
        have h7 : I ^ 4 = 1 := by
          norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
        calc
          I ^ (4 * n + 3) = (I ^ 4) ^ n * I ^ 3 := by ring
          _ = (1) ^ n * I ^ 3 := by rw [h7]
          _ = I ^ 3 := by ring
          _ = -I := by
            have h8 : I ^ 3 = -I := by
              calc
                I ^ 3 = I ^ 2 * I := by ring
                _ = (-1) * I := by simp [Complex.I_sq]
                _ = -I := by ring
            exact h8
      have h32 : I ^ (4 * n + 4) = 1 := by
        have h7 : I ^ 4 = 1 := by
          norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
        calc
          I ^ (4 * n + 4) = (I ^ 4) ^ (n + 1) := by ring
          _ = (1) ^ (n + 1) := by rw [h7]
          _ = 1 := by simp
      have h33 : I ^ (4 * n + 1) = I := by
        have h7 : I ^ 4 = 1 := by
          norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
        calc
          I ^ (4 * n + 1) = (I ^ 4) ^ n * I := by ring
          _ = (1) ^ n * I := by rw [h7]
          _ = I := by ring
      simp [pow_succ, h30, h31, h32, h33]
      all_goals ring_nf <;> simp [Complex.ext_iff, Complex.I_mul_I]
      all_goals ring

  have h34 : 4 * 503 + 1 = 2013 := by norm_num
  rw [show 2013 = 4 * 503 + 1 by omega]
  rw [h3 503]
  all_goals
    norm_num [Complex.ext_iff, mul_add, mul_assoc]