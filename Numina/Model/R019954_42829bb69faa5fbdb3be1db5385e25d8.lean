import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_183626 {a b : EuclideanSpace ℝ (Fin 3)}
  (ha : a = ![6, -8, 5 * sqrt 2]) (hb : b = ![2, -4, sqrt 2]) :
  let v := a - b
  let z := v 2
  let x := v 0
  let y := v 1
  let h := x^2 + y^2
  let h' := z^2
  let cosθ := z / sqrt (x^2 + y^2 + z^2)
  let θ := arccos cosθ
  θ = π / 4 := by
  have h1 : a = ![6, -8, 5 * sqrt 2] := ha
  have h2 : b = ![2, -4, sqrt 2] := hb
  have h3 : a - b = ![4, -4, 4 * sqrt 2] := by
    rw [h1, h2]
    funext i
    fin_cases i <;> simp [sub_mul] <;> ring
  -- Extracting coordinates
  have h4 : (a - b) 0 = 4 := by
    rw [h3]
    simp
  -- Extracting coordinates
  have h5 : (a - b) 1 = -4 := by
    rw [h3]
    simp
  -- Extracting coordinates
  have h6 : (a - b) 2 = 4 * sqrt 2 := by
    rw [h3]
    simp
  simp_all only [h3, h4, h5, h6]
  have h7 : (4 : ℝ) ^ 2 + (-4 : ℝ) ^ 2 + (4 * sqrt 2) ^ 2 = (64 : ℝ) := by
    have h8 : (sqrt (2 : ℝ)) ^ 2 = 2 := by
      exact sq_sqrt (by norm_num)
    nlinarith [h8, sq_nonneg (sqrt 2)]
  have h8 : Real.sqrt ((4 : ℝ) ^ 2 + (-4 : ℝ) ^ 2 + (4 * Real.sqrt (2 : ℝ)) ^ 2) = (8 : ℝ) := by
    rw [h7]
    exact Real.sqrt_eq_cases.mpr (by norm_num)
  have h9 : (4 * Real.sqrt (2 : ℝ)) / Real.sqrt ((4 : ℝ) ^ 2 + (-4 : ℝ) ^ 2 + (4 * Real.sqrt (2 : ℝ)) ^ 2) = Real.sqrt (2 : ℝ) / 2 := by
    rw [h8]
    have h11 : Real.sqrt (2 : ℝ) > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    field_simp
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h12 : Real.arccos (Real.sqrt (2 : ℝ) / 2) = Real.pi / 4 := by
    have h13 : Real.cos (Real.pi / 4 : ℝ) = Real.sqrt (2 : ℝ) / 2 := by
      exact Real.cos_pi_div_four
    rw [← h13]
    apply Real.arccos_cos
    all_goals linarith [Real.pi_pos]
  rw [h9]
  exact h12