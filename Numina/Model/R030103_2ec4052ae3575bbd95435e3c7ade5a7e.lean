import Mathlib

open Real

theorem algebra_102962 : {x : ℝ | x > 0 ∧ x^x + x^(1 - x) = x + 1} = {1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the left side, prove x = 1.
    intro h
    rcases h with ⟨hx_pos, heq⟩
    have eq1 : x^x + x^(1 - x) = x + 1 := heq
    have eq2 : x ^ (1 - x : ℝ) = x / x ^ x := by
      have h10 : x ^ (1 - x : ℝ) = x ^ (1 : ℝ) * x ^ (-x : ℝ) := by
        rw [← Real.rpow_add]
        ring
        all_goals
          linarith
      have h11 : x ^ (1 : ℝ) = x := by
        simp
      have h12 : x ^ (-x : ℝ) = 1 / (x ^ x : ℝ) := by
        have h13 : x ^ (-x : ℝ) = (x ^ x) ^ (-1 : ℝ) := by
          rw [← Real.rpow_mul]
          ring_nf
          all_goals
            linarith
        have h14 : (x ^ x : ℝ) ^ (-1 : ℝ) = 1 / (x ^ x : ℝ) := by
          simp [Real.rpow_neg_one]
        rw [h13, h14]
      rw [h10, h11, h12]
      field_simp
    rw [eq2] at eq1
    have eq3 : (x ^ x : ℝ) ^ 2 - (x + 1) * (x ^ x : ℝ) + x = (0 : ℝ) := by
      have h13 : x ^ x > 0 := by positivity
      field_simp at eq1 ⊢
      nlinarith [sq_pos_of_pos (show 0 < x ^ x by positivity)]
    have hy : ((x ^ x : ℝ) - x) * ((x ^ x : ℝ) - 1) = (0 : ℝ) := by
      nlinarith
    cases' (mul_eq_zero.1 hy) with hy1 hy2
    ·
      have h10 : x ^ x = x := by linarith
      have h11 : x * (Real.log x) = Real.log x := by
        have h100 : Real.log (x ^ x) = Real.log x := by
          rw [h10]
        have h101 : Real.log (x ^ x) = x * Real.log x := by
          rw [Real.log_rpow]
          all_goals
            try linarith
        linarith [h100, h101]
      have h13 : Real.log x * (x - 1) = 0 := by
        linarith
      cases' (mul_eq_zero.1 h13) with h14 h15
      ·
        have h16 : Real.log x = 0 := by linarith
        have h17 : x = 1 := by
          rw [Real.log_eq_zero] at h16
          rcases h16 with (r | r | r)
          · linarith
          · linarith
          · linarith
        linarith
      ·
        have h18 : x - 1 = 0 := by linarith
        have h19 : x = 1 := by linarith
        linarith
    ·
      have h10 : x ^ x = 1 := by linarith
      have h11 : x * (Real.log x) = 0 := by
        have h100 : Real.log (x ^ x) = Real.log (1 : ℝ) := by
          rw [h10]
        have h101 : Real.log (x ^ x) = x * Real.log x := by
          rw [Real.log_rpow]
          all_goals
            try linarith
        have h102 : Real.log (1 : ℝ) = 0 := by
          simp
        linarith [h100, h101, h102]
      have h13 : Real.log x = 0 := by
        nlinarith
      have h17 : x = 1 := by
        rw [Real.log_eq_zero] at h13
        rcases h13 with (r | r | r)
        · linarith
        · linarith
        · linarith
      linarith
  · -- Assume x = 1, prove x is in the left side.
    intro h
    rw [h]
    constructor
    · norm_num
    ·
      norm_num