import Mathlib

theorem algebra_162299 (k : ℝ) (hk : k > 0) (h : ∃ n m, n > 0 ∧ m > 0 ∧ |(n : ℤ) - m| = 4 ∧ Real.sqrt ((n * k - m * k)^2 + (n - m)^2) = 31) :
    Real.sqrt ((7 * k - 19 * k)^2 + (7 - 19)^2) = 93 := by
  rcases h with ⟨n, m, hn, hm, h1, h2⟩
  have h3 : ((n : ℤ) - m : ℤ) ^ 2 = 16 := by
    have h4 : |(n : ℤ) - m| = 4 := h1
    cases' eq_or_eq_neg_of_abs_eq h4 with h5 h6
    · -- The difference is 4 
      have : ((n : ℤ) - m : ℤ) = (4 : ℤ) := by linarith
      nlinarith
    · -- The difference is -4 
      have : ((n : ℤ) - m : ℤ) = (-4 : ℤ) := by linarith
      nlinarith
  have h4 : (n - m : ℝ) ^ 2 = (16 : ℝ) := by
    have h5 : (n : ℝ) - (m : ℝ) = ((n : ℤ) - (m : ℤ) : ℝ) := by simp
    rw [h5]
    exact_mod_cast h3
  have h5 : (n * k - m * k) ^ 2 + (n - m : ℝ) ^ 2 = (961 : ℝ) := by
    have h6 : Real.sqrt ((n * k - m * k) ^ 2 + (n - m) ^ 2) = (31 : ℝ) := h2
    have h7 : (Real.sqrt ((n * k - m * k) ^ 2 + (n - m) ^ 2)) ^ 2 = (31 : ℝ) ^ 2 := by 
      rw [h6]
    have h8 : (Real.sqrt ((n * k - m * k) ^ 2 + (n - m) ^ 2)) ^ 2 = ((n * k - m * k) ^ 2 + (n - m) ^ 2) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith
  have hk2 : k^2 = 945 / 16 := by
    have h6 : (n * k - m * k) ^ 2 + (n - m) ^ 2 = (16 * (k^2) + 16) := by
      have h7 : (n * k - m * k) ^ 2 = (k * (n - m)) ^ 2 := by ring
      rw [h7]
      have h8 : (n - m : ℝ) ^ 2 = (16 : ℝ) := h4
      nlinarith [h8]
    nlinarith
  have h71 : (7 * k - 19 * k) ^ 2 + (7 - 19 : ℝ) ^ 2 = (8649 : ℝ) := by
    nlinarith [hk2]
  have h72 : Real.sqrt ((7 * k - 19 * k) ^ 2 + (7 - 19 : ℝ) ^ 2) = 93 := by
    rw [h71]
    have h73 : Real.sqrt ((8649 : ℝ)) = 93 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h73
  exact h72