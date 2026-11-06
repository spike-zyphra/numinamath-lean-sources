import Mathlib

theorem algebra_230410 :
    {x : ℝ | 0 ≤ x + 5 ∧ 2 * x + 8 ≥ 0 ∧ Real.sqrt (2 * x + 8) - Real.sqrt (x + 5) = 7} = {284} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Forward direction: if x is in the set, then x = 284
    rintro ⟨hx1, hx2, heq⟩
    have h1 : Real.sqrt (2 * x + 8) = Real.sqrt (x + 5) + 7 := by linarith
    have h2 : (Real.sqrt (2 * x + 8)) ^ 2 = (Real.sqrt (x + 5) + 7) ^ 2 := by
      rw [h1]
    have h3 : (Real.sqrt (2 * x + 8)) ^ 2 = 2 * x + 8 := Real.sq_sqrt (by linarith)
    have h4 : (Real.sqrt (x + 5) + 7) ^ 2 = (Real.sqrt (x + 5)) ^ 2 + 14 * (Real.sqrt (x + 5)) + 49 := by
      ring
    have h5 : (Real.sqrt (x + 5)) ^ 2 = x + 5 := Real.sq_sqrt (by linarith)
    rw [h3, h4, h5] at h2
    have h6 : x - 46 = 14 * (Real.sqrt (x + 5)) := by
      nlinarith
    have h7 : (x - 46) ^ 2 = (14 * (Real.sqrt (x + 5)) ) ^ 2 := by
      rw [h6]
    have h8 : (14 * (Real.sqrt (x + 5)) ) ^ 2 = 196 * ( (Real.sqrt (x + 5)) ^ 2 ) := by
      ring_nf
    have h9 : (Real.sqrt (x + 5)) ^ 2 = x + 5 := Real.sq_sqrt (by linarith)
    have h10 : (x - 46) ^ 2 = x^2 - 92 * x + 2116 := by
      ring
    rw [h10] at h7
    rw [h8, h9] at h7
    have h11 : x ^ 2 - 288 * x + 1136 = 0 := by
      nlinarith
    have h12 : (x - 284) * (x - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- x - 284 = 0
      linarith
    · -- x - 4 = 0
      have hx4 : x = 4 := by linarith
      rw [hx4] at heq
      have h14 : Real.sqrt (2 * (4 : ℝ) + 8) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h15 : Real.sqrt (4 + 5) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h14, h15] at heq
      all_goals nlinarith
  · -- Backward direction: if x = 284, then x is in the set
    intro hx
    rw [hx]
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show that $\sqrt{2x+8} - \sqrt{x+5} = 7$
      have h14 : Real.sqrt (2 * (284 : ℝ) + 8) = (24 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h15 : Real.sqrt (284 + 5) = (17 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h14, h15]
      all_goals norm_num