import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_20564 {z w : ℂ} (hz : z = 1 + .I) (hw : w = (3 * z + 1) / (5 * z + 7)) :
    abs w = 5 / 13 := by
  rw [hw, hz]
  have h1 : (3 * (1 + Complex.I) + 1 : ℂ) = 4 + 3 * Complex.I := by
    ring_nf
  have h2 : (5 * (1 + Complex.I) + 7 : ℂ) = 12 + 5 * Complex.I := by
    ring_nf
  rw [h1, h2]
  have h3 : abs ((4 + 3 * Complex.I : ℂ) / (12 + 5 * Complex.I : ℂ)) =
    abs ((4 + 3 * Complex.I : ℂ)) / abs ((12 + 5 * Complex.I : ℂ)) := by
    field_simp [Complex.abs]
  rw [h3]
  have h4 : abs ((4 + 3 * Complex.I : ℂ)) = 5 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    norm_num [Real.sqrt_eq_iff_sq_eq]
  have h5 : abs ((12 + 5 * Complex.I : ℂ)) = 13 := by
    simp [Complex.abs, Complex.normSq]
    ring_nf
    norm_num [Real.sqrt_eq_iff_sq_eq]
  rw [h4, h5]
  all_goals norm_num