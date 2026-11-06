import Mathlib

/-
  Solve for the real value of $x$ in the equation $9^{x}+3^{x}-6=0$.
-/
theorem algebra_9448 (x : ℝ) : 9 ^ x + 3 ^ x - 6 = (0 : ℝ) ↔ x = Real.logb 3 2 := by
  -- First we reform 9 ^ x as (3 ^ x) ^ 2
  have : 9 ^ x = ((3 ^ x) ^ 2 : ℝ) := by calc
    (9 ^ x : ℝ) = (3 ^ 2) ^ x := by norm_num
    _ = 3 ^ (2 * x) := by simp [Real.rpow_mul]
    _ = 3 ^ (x * 2) := by rw [mul_comm]
    _ = (3 ^ x) ^ 2 := by simp [Real.rpow_mul]
  rw [this]

  constructor
  · -- 'if' part
    intro h
    -- we only need to show 3 ^ x = 2, which would imply x = log 3 2
    suffices goal : 3 ^ x = (2 : ℝ) from by
      have hbase : 3 > (0 : ℝ) := by norm_num
      have hbase' : 3 ≠ (1 : ℝ) := by norm_num
      have hexp : 2 > (0 : ℝ) := by norm_num
      exact ((Real.logb_eq_iff_rpow_eq hbase hbase' hexp).mpr goal).symm

    let y : ℝ := 3 ^ x
    rw [(by rfl : 3 ^ x = y)] at *

    -- factorize the formula
    have : y ^ 2 + y - 6 = (y + 3) * (y - 2) := by ring
    rw [this] at h
    -- now y = -3 or y = 2, but the former is impossible, since y = 3 ^ x > 0
    rcases mul_eq_zero.mp h with h | h
    · have : y = (-3 : ℝ) := by exact eq_neg_of_add_eq_zero_left h
      have : y < 0 := by rw [this]; norm_num
      have : y > 0 := by simp [y]; apply Real.rpow_pos_of_pos; norm_num
      linarith
    · exact sub_eq_zero.mp h

  · -- 'only if' part, just do the calculation
    intros; simp_all; norm_num