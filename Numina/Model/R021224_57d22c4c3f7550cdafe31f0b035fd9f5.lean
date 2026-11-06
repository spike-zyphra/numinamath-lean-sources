import Mathlib

theorem algebra_144345 (A B C : EuclideanSpace ℝ (Fin 3))
    (hA : A = ![1, -1, 0]) (hB : B = ![-2, -1, 4]) (hC : C = ![8, -1, -1]) :
    let v1 := B - A
    let v2 := C - A
    let cosθ := (inner v1 v2) / (norm v1 * norm v2)
    cosθ = -1 / Real.sqrt 2 := by
  -- let v1 := B - A
  -- let v2 := C - A
  -- let cosθ := (inner v1 v2) / (norm v1 * norm v2)
  -- cosθ = -1 / Real.sqrt 2
  rw [hA] at *
  rw [hB] at *
  rw [hC] at *
  -- Compute inner product v1 ⋅ v2 = -25
  -- Compute norm v1 = 5
  -- Compute norm v2 = 5 * Real.sqrt 2
  -- Then cosθ = (-25) / (5 * 5 * Real.sqrt 2) = -1 / Real.sqrt 2
  simp [Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  ring_nf
  have h1 : Real.sqrt 25 = (5 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt (50 : ℝ) = (5 : ℝ) * Real.sqrt 2 := by
    calc
      Real.sqrt (50 : ℝ) = Real.sqrt (2 * (25 : ℝ)) := by
        ring_nf
      _ = Real.sqrt 2 * Real.sqrt (25 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 2 * (5 : ℝ) := by
        have h : Real.sqrt (25 : ℝ) = (5 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h]
        <;> norm_num
      _ = (5 : ℝ) * Real.sqrt 2 := by ring
  field_simp [h1, h2]
  <;> ring_nf
  <;> field_simp
  <;> ring_nf <;> norm_num
  all_goals norm_num
  all_goals tauto
  all_goals try { norm_cast }
  all_goals try { linarith }
  all_goals try { tauto }
  all_goals try { nlinarith }