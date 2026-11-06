import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_11684 {z w : ℂ}
  (hz : z = ((-11 + 13 * .I)^3 * (24 - 7 * .I)^4) / (3 + 4 * .I))
  (hw : w = z⁻¹ * (z.re - z.im * .I)) :
  abs w = 1 := by
  rw [hw]
  have hz1 : z ≠ 0 := by
    rw [hz]
    norm_num [Complex.ext_iff]
    all_goals norm_num
    <;> try { norm_num }
  have h1 : abs (z⁻¹) = 1 / abs z := by 
    simp [Complex.abs, Complex.normSq, hz1]
    <;> field_simp [hz1]
    <;> norm_num [Complex.ext_iff] at *
    all_goals norm_num
  have h2 : abs (z.re - z.im * Complex.I) = abs z := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num [Complex.ext_iff] at *
    all_goals norm_num
  have hw1 : abs (z⁻¹ * (z.re - z.im * Complex.I)) = abs (z⁻¹) * abs (z.re - z.im * Complex.I) := by
    simp [Complex.abs, abs_mul]
  rw [hw1]
  rw [h1, h2]
  field_simp [hz1]
  all_goals norm_num
  all_goals norm_num [Complex.ext_iff] at *
  all_goals norm_num