import Mathlib

theorem algebra_16738 {s : ℝ} (hs : 0 < s) (h : 3 * Real.logb 2 s = Real.logb 2 (3 * s)) :
    s = Real.sqrt 3 := by
  have h1 : Real.logb 2 (3 * s) = Real.logb 2 3 + Real.logb 2 s := by
    rw [Real.logb_mul (by norm_num) (by linarith)]
  rw [h1] at h
  have h2 : 2 * Real.logb 2 s = Real.logb 2 3 := by
    linarith
  have h3 : 2 * Real.logb 2 s = Real.logb 2 (s ^ 2) := by
    simp [Real.logb_pow]
    <;> ring_nf <;> norm_num
  rw [h3] at h2
  have h4 : s ^ 2 = 3 := by
    have h5 : Real.logb 2 (s ^ 2) = Real.logb 2 3 := h2
    have h6 : s ^ 2 > 0 := by
      positivity
    have h7 : (3 : ℝ) > 0 := by
      norm_num
    have h8 : s ^ 2 = (3 : ℝ) := by
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h6) (Set.mem_Ioi.mpr h7) h5
    linarith
  have h9 : s > 0 := by linarith
  have h10 : s = Real.sqrt 3 := by
    have h11 : s ^ 2 = 3 := h4
    have h12 : s > 0 := h9
    have h13 : s = Real.sqrt 3 := by
      rw [←h11]
      field_simp
    exact h13
  exact h10