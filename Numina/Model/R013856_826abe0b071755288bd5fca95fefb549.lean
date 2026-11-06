import Mathlib

theorem algebra_165296 {a q1 q2 : ℝ} {S1 S2 : ℝ}
    (hq1 : |q1| < 1) (hq2 : |q2| < 1)
    (hS1 : S1 = a / (1 - q1)) (hS2 : S2 = a / (1 - q2))
    (h : q1 = -q2) :
    ∑' n : ℕ, (a * q1 ^ n) ^ 2 = S1 * S2 := by
  have hq2_eq : q2 = -q1 := by
    linarith [h]

  have hS2' : S2 = a / (1 + q1) := by 
    rw [hS2]
    rw [hq2_eq]
    have h1 : 1 - (-q1) = 1 + q1 := by ring
    rw [h1]
    all_goals try field_simp
    all_goals try ring_nf
    all_goals try nlinarith


  have h1 : ∑' n : ℕ, (a * q1 ^ n) ^ 2 = a^2 / (1 - q1^2) := by
    have h3 : |q1 ^ 2| < 1 := by
      have h4 : |q1| < 1 := hq1
      have h5 : |q1| ≥ 0 := by apply abs_nonneg
      have h6 : |q1| ^ 2 < 1 := by nlinarith [abs_nonneg (q1), h4]
      have : |q1 ^ 2| = |q1| ^ 2 := by
        simp [abs_pow]
        <;> try linarith
      rw [this]
      nlinarith
    have h7 : ∑' n : ℕ, (a * q1 ^ n) ^ 2 = ∑' n : ℕ, a^2 * (q1^2) ^ n := by 
      congr 1
      funext n
      ring_nf 
    rw [h7]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring_nf
    · simpa using h3
  rw [h1]
  rw [hS1]
  rw [hS2']
  have h3 : 1 - q1^2 ≠ 0 := by
    by_contra h'
    have h4 : q1^2 = 1 := by nlinarith
    have h5 : |q1| = 1 := by
      have : |q1| = Real.sqrt (q1 ^ 2) := by 
        rw [Real.sqrt_sq_eq_abs]
      rw [this, h4]
      norm_num
      all_goals try linarith
    have h6 : |q1| < 1 := hq1
    linarith [abs_nonneg (q1), h6, h5]

  have h6 : (1 - q1) ≠ 0 := by
    by_contra h'
    have h9 : q1 = 1 := by linarith
    have h10 : |q1| = 1 := by
      rw [h9]
      norm_num
    have h11 : |q1| < 1 := hq1
    linarith [abs_nonneg (q1), h11, h10]

  have h7 : (1 + q1) ≠ 0 := by
    by_contra h'
    have h11 : q1 = -1 := by linarith
    have h12 : |q1| = 1 := by
      rw [h11]
      norm_num [abs]
    have h13 : |q1| < 1 := hq1
    linarith [abs_nonneg (q1), h13, h12]

  field_simp [(show (1 - q1 : ℝ) ≠ 0 by assumption), (show (1 + q1 : ℝ) ≠ 0 by assumption), (show (1 - q1^2 : ℝ) ≠ 0 by assumption)]
  <;> ring_nf <;> field_simp [(show (1 - q1^2 : ℝ) ≠ 0 by assumption)]
  <;> ring
  all_goals try nlinarith
  all_goals try tauto
  all_goals try nlinarith
  all_goals try tauto