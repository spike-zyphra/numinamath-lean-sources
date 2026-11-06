import Mathlib

theorem algebra_13274 (a : ℝ) (ha : a > 0) (h : √3 * a = 2 * √6) :
    (1 / 2) * a * √6 = 2 * √3 := by
  have ha_eq : a = (2 * √6) / √3 := by
    field_simp
    nlinarith
  rw [ha_eq]
  have h1 : (1 / 2 : ℝ) * ((2 * √6) / √3) * √6 = (1 / 2 : ℝ) * (12 / √3) := by
    field_simp
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1]
  have h2 : (12 : ℝ) / √3 = 4 * √3 := by
    have h3 : (12 : ℝ) / √3 = (12 / 3) * √3 := by
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h3]
    ring_nf
    <;> norm_num
    <;> ring_nf <;> norm_num
    all_goals norm_num
  have h3 : (1 / 2 : ℝ) * ((12 / √3) : ℝ) = (1 / 2 : ℝ) * (4 * √3) := by rw [h2]
  rw [h3]
  ring_nf
  <;> norm_num
  <;> ring_nf <;> norm_num