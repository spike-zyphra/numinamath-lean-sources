import Mathlib

open Real

theorem inequalities_41908 :
    IsGreatest {x | ∃ p q r s : ℝ, p^2 + q^2 + r^2 - s^2 + 4 = 0 ∧ x = 3 * p + 2 * q + r - 4 * abs s} (-2 * sqrt 2) := by 
  constructor
  · -- Show that -2 * sqrt 2 is in the set.
    use 3 * sqrt 2, 2 * sqrt 2, sqrt 2, 4 * sqrt 2
    constructor
    · -- Verify constraint.
      norm_num
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · -- Verify value.
      have h_abs : abs (4 * sqrt 2) = 4 * sqrt 2 := by
        apply abs_of_nonneg
        positivity
      rw [h_abs]
      <;> ring_nf <;> simp [Real.sq_sqrt]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show that -2 * sqrt 2 is greatest in the set.
    rintro x ⟨p, q, r, s, h_eq, hx⟩
    have h_eq' : p^2 + q^2 + r^2 = s^2 - 4 := by linarith [h_eq]
    have h1 : (3 * p + 2 * q + r) ^ 2 ≤ (3 ^ 2 + 2 ^ 2 + 1 ^ 2) * (p^2 + q^2 + r^2) := by
      nlinarith [sq_nonneg (3 * q - 2 * p), sq_nonneg (3 * r - 1 * p), sq_nonneg (2 * r - 1 * q), sq_nonneg (p + q + r), sq_nonneg (3 * q - 2 * p), sq_nonneg (3 * r - 1 * p), sq_nonneg (2 * r - 1 * q)]
    have h2 : (3 * p + 2 * q + r) ≤ Real.sqrt ((3 ^ 2 + 2 ^ 2 + 1 ^ 2) * (p^2 + q^2 + r^2)) := by
      have h1' : (3 * p + 2 * q + r) ^ 2 ≤ (3 ^ 2 + 2 ^ 2 + 1 ^ 2) * (p^2 + q^2 + r^2) := h1
      have h2 : (3 * p + 2 * q + r) ≤ Real.sqrt ((3 ^ 2 + 2 ^ 2 + 1 ^ 2) * (p^2 + q^2 + r^2)) := by
        apply Real.le_sqrt_of_sq_le
        linarith [h1']
      linarith [h2]
    have h3 : Real.sqrt ((3 ^ 2 + 2 ^ 2 + 1 ^ 2 : ℝ) * (p^2 + q^2 + r^2)) = Real.sqrt ((14 : ℝ) * (s^2 - 4)) := by
      rw [show (3 ^ 2 + 2 ^ 2 + 1 ^ 2 : ℝ) = 14 by norm_num, h_eq']
      <;> rfl
    rw [h3] at h2
    cases' abs_cases s with h4 h4
    · -- Case where s ≥ 0, so |s| = s
      have h3 : x = (3 * p + 2 * q + r) - 4 * s := by
        rw [hx]
        all_goals 
          linarith [h4]
      rw [h3]
      -- Now we need to bound the expression.
      have h4 : s ^ 2 ≥ 4 := by
        nlinarith [sq_nonneg (p ^ 2 + q ^ 2 + r ^ 2)]
      have h5 : s ≥ 0 := by linarith
      -- Use Cauchy-Schwarz and solve for maximum.
      nlinarith [sq_nonneg (s - 4 * Real.sqrt 2), sq_nonneg (p - 3 * Real.sqrt 2), sq_nonneg (q - 2 * Real.sqrt 2), sq_nonneg (r - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    · -- Case where s < 0, so |s| = -s
      have h3 : x = (3 * p + 2 * q + r) + 4 * s := by
        rw [hx]
        all_goals
          linarith [h4]
      rw [h3]
      -- Now we need to bound the expression.
      have h4 : s ^ 2 ≥ 4 := by
        nlinarith [sq_nonneg (p ^ 2 + q ^ 2 + r ^ 2)]
      have h5 : s ≤ 0 := by linarith
      -- Use Cauchy-Schwarz and solve for maximum.
      nlinarith [sq_nonneg (s + 4 * Real.sqrt 2), sq_nonneg (p - 3 * Real.sqrt 2), sq_nonneg (q - 2 * Real.sqrt 2), sq_nonneg (r - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (Real.sqrt 2 + 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (p ^ 2 + q ^ 2 + r^2)]
    all_goals 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (p ^ 2 + q ^ 2 + r^2)]