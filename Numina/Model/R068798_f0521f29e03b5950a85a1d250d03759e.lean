import Mathlib

theorem algebra_322643 {x : ℝ} (hx : x = (Real.sqrt 5 + 1) / 2) :
    (x^3 + x + 1) / x^5 = (Real.sqrt 5 - 1) / 2 := by
  have h1 : x ^ 2 = x + 1 := by
    rw [hx]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 5 ≥ 0 by norm_num)]
  have hx2 : x ^ 2 = x + 1 := h1
  have hx3 : x ^ 3 = 2 * x + 1 := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * (x + 1) := by rw [h1]
      _ = x ^ 2 + x := by ring
      _ = (x + 1) + x := by rw [h1]
      _ = 2 * x + 1 := by ring
  have hx4 : x ^ 4 = 3 * x + 2 := by
    calc
      x ^ 4 = x * x ^ 3 := by ring
      _ = x * (2 * x + 1) := by rw [hx3]
      _ = 2 * x ^ 2 + x := by ring
      _ = 2 * (x + 1) + x := by rw [h1]
      _ = 3 * x + 2 := by ring
  have hx5 : x ^ 5 = 5 * x + 3 := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ = x * (3 * x + 2) := by rw [hx4]
      _ = 3 * x ^ 2 + 2 * x := by ring
      _ = 3 * (x + 1) + 2 * x := by rw [h1]
      _ = 5 * x + 3 := by ring
  rw [hx5] 
  have h_num : x ^ 3 + x + 1 = 3 * x + 2 := by
    nlinarith [hx3]
  rw [h_num]
  rw [hx]
  field_simp
  <;> ring_nf <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 5 ≥ 0 by norm_num)]
  all_goals nlinarith
  <;> field_simp
  <;> nlinarith
  <;> field_simp
  <;> nlinarith
  <;> field_simp
  <;> nlinarith
  <;> field_simp
  <;> nlinarith