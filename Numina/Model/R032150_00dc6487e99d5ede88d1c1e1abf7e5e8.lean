import Mathlib

theorem algebra_97357 (x : ℕ → ℝ) (h : ∀ i ∈ Finset.Icc 4 127, x i = Real.logb i (i + 1)) :
    ∏ i ∈ Finset.Icc 4 127, x i = 7 / 2 := by
  have h1 : ∀ i ∈ Finset.Icc 4 127, x i = Real.log (i + 1) / Real.log (i : ℕ) := by
    intro i hi
    rw [h i hi]
    simp [Real.logb]
    all_goals norm_num
  have h3 : ∏ i in Finset.Icc 4 127, x i = Real.log 128 / Real.log 4 := by
    have eq1 : ∀ i ∈ Finset.Icc 4 127, x i = Real.log (i + 1) / Real.log (i : ℕ) := h1
    rw [Finset.prod_congr rfl (fun i hi => eq1 i hi)]
    norm_num [Finset.prod_Icc_succ_top]
    <;> field_simp <;> ring_nf <;> simp [Real.log_pow] <;> field_simp <;> ring
    <;> field_simp <;> linarith
  have h4 : Real.log 128 = 7 * Real.log 2 := by
    calc
      Real.log 128 = Real.log (2 ^ 7 : ℝ) := by norm_num
      _ = 7 * Real.log 2 := by simp [Real.log_pow]
  have h5 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log (2 ^ 2 : ℝ) := by norm_num
      _ = 2 * Real.log 2 := by simp [Real.log_pow]
  have h6 : Real.log 2 > 0 := by
    apply Real.log_pos
    all_goals norm_num
  rw [h3, h4, h5]
  field_simp [show Real.log 2 ≠ 0 by linarith]
  <;> linarith