import Mathlib

theorem algebra_321025 (a : ℝ) (ha : 0 < abs a ∧ abs a < 1) :
    (a + 1) / (a + 1 - Real.sqrt (1 - a ^ 2)) +
    (a - 1) / (Real.sqrt (1 - a ^ 2) + a - 1) = 1 := by
  rcases ha with ⟨ha1, ha2⟩
  have h1 : a ^ 2 < 1 := by
    have h2 : abs a < 1 := ha2
    have h3 : -(1 : ℝ) < a := by
      linarith [abs_lt.mp h2]
    have h4 : a < (1 : ℝ) := by
      linarith [abs_lt.mp h2]
    nlinarith [abs_nonneg a, abs_lt.mp h2]
  have h2 : 0 ≤ 1 - a ^ 2 := by
    nlinarith
  have h4 : a ≠ 0 := by
    by_contra h
    have : abs a = 0 := by
      rw [h]
      norm_num
    linarith [ha1, this]
  have h5 : a + 1 - Real.sqrt (1 - a ^ 2) ≠ 0 := by
    by_contra h
    have h6 : Real.sqrt (1 - a ^ 2) = a + 1 := by
      linarith
    have h7 : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h8 : (a + 1) ^ 2 = 1 - a ^ 2 := by
      calc
        (a + 1) ^ 2 = Real.sqrt (1 - a ^ 2) ^ 2 := by rw [h6]
        _ = 1 - a ^ 2 := by rw [Real.sq_sqrt (by nlinarith)]
    have h9 : 2 * a * (a + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Case a =0
      have h12 : a = 0 := by
        linarith
      contradiction
    · -- Case a+1=0, i.e., a=-1
      have h13 : a = -1 := by
        linarith
      have h14 : abs a = 1 := by
        rw [h13]
        norm_num
      linarith [ha2, h14]
  have h6 : Real.sqrt (1 - a ^ 2) + a - 1 ≠ 0 := by
    by_contra h
    have h7 : Real.sqrt (1 - a ^ 2) = 1 - a := by
      linarith
    have h7 : Real.sqrt (1 - a ^ 2) = 1 - a := by
      linarith
    have h8 : Real.sqrt (1 - a ^ 2) ^ 2 = 1 - a ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h9 : (1 - a) ^ 2 = 1 - a ^ 2 := by
      calc
        (1 - a) ^ 2 = Real.sqrt (1 - a ^ 2) ^ 2 := by rw [h7]
        _ = 1 - a ^ 2 := by rw [Real.sq_sqrt (by nlinarith)]
    have h10 : 2 * a * (a - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case a =0
      have h13 : a = 0 := by
        linarith
      contradiction
    · -- Case a-1=0, i.e., a=1
      have h14 : a = 1 := by
        linarith
      have h15 : abs a = 1 := by
        rw [h14]
        norm_num
      linarith [ha2, h15]
  field_simp [(show a + 1 - Real.sqrt (1 - a ^ 2) ≠ 0 by exact h5), (show Real.sqrt (1 - a ^ 2) + a - 1 ≠ 0 by exact h6)]
  <;> nlinarith [Real.sqrt_nonneg (1 - a ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - a ^ 2 by nlinarith), sq_nonneg (a ^ 2 - 1), sq_nonneg (a - 0), sq_nonneg (Real.sqrt (1 - a ^ 2) - (a)), sq_nonneg (Real.sqrt (1 - a ^ 2) + a)]