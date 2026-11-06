import Mathlib

theorem algebra_315306 {a : ℝ} (ha : a ≠ 0) (h : a - 4 / a + 3 * √(a * (a - 2)) / a = 2) :
    ⌊a⌋ = -1 ∨ ⌊a⌋ = 2 := by
  have h1 : a * (a - 4 / a + 3 * Real.sqrt (a * (a - 2)) / a) = a * (2) := by
    rw [h]
    all_goals norm_num
    all_goals nlinarith
  have h2 : a * (a - 4 / a + 3 * Real.sqrt (a * (a - 2)) / a) = a^2 - 4 + 3 * Real.sqrt (a * (a - 2)) := by
    field_simp
    <;> ring_nf <;> field_simp
    <;> ring
  rw [h2] at h1
  have h3 : 0 ≤ a * (a - 2) := by
    by_contra h3
    push_neg at h3
    have h4 : Real.sqrt (a * (a - 2)) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals nlinarith
    rw [h4] at h1
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact ha)]
  -- h5 proves the equality `sq_sqrt` since `a * (a - 2) >=0` is now proven
  have h5 : (Real.sqrt (a * (a - 2))) ^ 2 = a * (a - 2) := Real.sq_sqrt (by nlinarith)
  have heq : a ^ 2 - 2 * a - 4 + 3 * Real.sqrt (a * (a - 2)) = 0 := by
    nlinarith
  have heq1 : (Real.sqrt (a * (a - 2)))^2 = a ^ 2 - 2 * a := by
    nlinarith
  have h7 : (Real.sqrt (a * (a - 2)) - 1) * (Real.sqrt (a * (a - 2)) + 4) = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (a * (a - 2))), sq_nonneg (a ^ 2 - 2 * a)]
  cases' (mul_eq_zero.1 h7) with h8 h9
  · -- Real.sqrt (a * (a - 2)) - 1 = 0
    have h10 : Real.sqrt (a * (a - 2)) = 1 := by linarith
    have h11 : a * (a - 2) = 1 := by
      nlinarith [Real.sqrt_nonneg (a * (a - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ a * (a - 2) by nlinarith)]
    have h12 : (a - (1 + Real.sqrt 2)) * (a - (1 - Real.sqrt 2)) = 0 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a ^ 2 - 2 * a)]
    cases' (mul_eq_zero.1 h12) with h13 h14
    · -- a - (1 + Real.sqrt 2) = 0
      have h15 : a = (1 + Real.sqrt 2 : ℝ) := by linarith
      have h16 : ⌊a⌋ = 2 := by
        rw [h15]
        have h17 : ⌊(1 + Real.sqrt (2 : ℝ) : ℝ)⌋ = 2 := by
          have h18 : 1 < Real.sqrt (2 : ℝ) := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h19 : Real.sqrt (2 : ℝ) < (2 : ℝ) := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h20 : 2 ≤ (1 + Real.sqrt (2 : ℝ) : ℝ) := by
            nlinarith
          have h21 : (1 + Real.sqrt (2 : ℝ) : ℝ) < (3 : ℝ) := by
            nlinarith
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> try linarith
        exact h17
      right
      tauto
    · -- a - (1 - Real.sqrt 2) = 0
      have h16 : a = (1 - Real.sqrt 2 : ℝ) := by linarith
      have h17 : ⌊a⌋ = -1 := by
        rw [h16]
        have h18 : ⌊(1 - Real.sqrt (2 : ℝ) : ℝ)⌋ = -1 := by
          have h19 : -1 ≤ (1 - Real.sqrt (2 : ℝ) : ℝ) := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h20 : (1 - Real.sqrt (2 : ℝ) : ℝ) < (0 : ℝ) := by
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> try linarith
        exact h18
      left
      tauto
  · -- Real.sqrt (a * (a - 2)) + 4 = 0
    have h10 : Real.sqrt (a * (a - 2)) = -4 := by linarith
    nlinarith [Real.sqrt_nonneg (a * (a - 2))]