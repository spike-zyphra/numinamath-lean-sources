import Mathlib

open Real

theorem inequalities_599389 (p : ℝ) (hp : 0 < p ∧ p < 1) (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.Icc 1 n, i * p^(i - 1) < 1 / (1 - p)^2 := by
  rcases hp with ⟨hp_pos, hp_lt_one⟩
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, i * p^(i - 1) = (1 - (n + 1) * p^n + n * p^(n + 1)) / (1 - p)^2 := by
    intro n
    induction n with
    | zero =>
      simp
      <;> field_simp [(show (1 - p) ≠ 0 by nlinarith)]
      <;> ring_nf <;> norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      rw [ih]
      simp [pow_succ, mul_add, add_mul]
      field_simp [(show (1 - p) ≠ 0 by nlinarith)]
      ring_nf
      <;> norm_num
      <;> ring
  have h2 := h1 n
  rw [h2]
  have h3 : (1 - (n + 1) * p^n + n * p^(n + 1) : ℝ) < (1 : ℝ) := by
    have h4 : (n : ℝ) * p ^ (n + 1) < (n + 1 : ℝ) * p ^ n := by
      have hp_pow_pos : 0 < (p : ℝ) ^ n := by
        positivity
      have h5 : (n : ℝ) * p ^ (n + 1) - (n + 1 : ℝ) * p ^ n < 0 := by 
        have h6 : (n : ℝ) * p ^ (n + 1) - (n + 1 : ℝ) * p ^ n =
          (p ^ n) * ( (n : ℝ) * p - (n + 1 : ℝ) ) := by ring
        rw [h6]
        have h7 : (n : ℝ) * p - (n + 1 : ℝ) < 0 := by
          nlinarith
        have hp_pow_pos : 0 < (p : ℝ) ^ n := by
          positivity
        nlinarith
      linarith
    nlinarith [show 0 < (p : ℝ) ^ n by positivity ]
  have h9 : 0 < (1 - p)^2 := by nlinarith
  apply (div_lt_div_right h9).mpr
  linarith