import Mathlib


open Real


lemma lemma_1 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x * Real.sqrt x + y * Real.sqrt y = (Real.sqrt x + Real.sqrt y) * (x - Real.sqrt (x * y) + y) := by
  have hx2 : 0 < (x : ℝ) := hx
  have hy2 : 0 < (y : ℝ) := hy
  have h7 : 0 < (x * y : ℝ) := mul_pos hx hy
  have h3 : 0 ≤ (x : ℝ) := by linarith
  have h4 : 0 ≤ (y : ℝ) := by linarith
  have h88 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
    rw [Real.sqrt_mul (by positivity)]
    all_goals positivity
  have h1 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
  have h2 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)
  have hx9 : (Real.sqrt x) ^ 3 = x * Real.sqrt x := by
    calc
      (Real.sqrt x) ^ 3 = (Real.sqrt x) ^ 2 * Real.sqrt x := by ring
      _ = x * Real.sqrt x := by
        rw [show (Real.sqrt x) ^ 2 = x by exact Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)]
        all_goals positivity
  have hy9 : (Real.sqrt y) ^ 3 = y * Real.sqrt y := by
    calc
      (Real.sqrt y) ^ 3 = (Real.sqrt y) ^ 2 * Real.sqrt y := by ring
      _ = y * Real.sqrt y := by
        rw [show (Real.sqrt y) ^ 2 = y by exact Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)]
        all_goals positivity
  calc
    x * Real.sqrt x + y * Real.sqrt y = (Real.sqrt x) ^ 3 + (Real.sqrt y) ^ 3 := by
      rw [hx9, hy9]
      all_goals linarith
    _ = (Real.sqrt x + Real.sqrt y) * (Real.sqrt x ^ 2 - (Real.sqrt x * Real.sqrt y) + (Real.sqrt y) ^ 2) := by
      ring_nf
    _ = (Real.sqrt x + Real.sqrt y) * (x - (Real.sqrt x * Real.sqrt y) + y) := by
      have h9 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
      have h10 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)
      rw [h9, h10]
      all_goals linarith
    _ = (Real.sqrt x + Real.sqrt y) * (x - Real.sqrt (x * y) + y) := by
      rw [show Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y by
        rw [Real.sqrt_mul (by positivity)]
        all_goals positivity
      ]
      all_goals linarith


theorem algebra_323516 (x y : ℝ) (hx : x > 0) (hy : y > 0) (hxy : x ≠ y) :
    ((Real.sqrt x - Real.sqrt y)^3 + 2 * x * Real.sqrt x + y * Real.sqrt y) /
    (x * Real.sqrt x + y * Real.sqrt y) + (3 * Real.sqrt (x * y) - 3 * y) / (x - y) = 3 := by
  have h1 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
    rw [Real.sqrt_mul (by positivity)]
    <;> all_goals positivity

  have hx01 : x - y ≠ 0 := by
    intro h
    apply hxy
    linarith

  have hx02 : x * Real.sqrt x + y * Real.sqrt y > 0 := by
    positivity

  have eq1 : ((Real.sqrt x - Real.sqrt y) ^3 + 2 * x * Real.sqrt x + y * Real.sqrt y) / (x * Real.sqrt x + y * Real.sqrt y) + (3 * Real.sqrt (x * y) - 3 * y) / (x - y) = 3 := by
    have eq2 : (3 * Real.sqrt (x * y) - 3 * y) = 3 * (Real.sqrt x * Real.sqrt y - y) := by
      rw [show Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y by linarith [h1]]
      <;> ring

    have eq3 : ((Real.sqrt x - Real.sqrt y) ^3 + 2 * x * Real.sqrt x + y * Real.sqrt y) = 3 * (x * Real.sqrt x - x * Real.sqrt y + y * Real.sqrt x) := by
      have h4 : (Real.sqrt x - Real.sqrt y) ^3 = Real.sqrt x ^3 - 3 * Real.sqrt x ^2 * Real.sqrt y + 3 * Real.sqrt x * Real.sqrt y ^2 - Real.sqrt y ^3 := by
        ring_nf
      have h5 : Real.sqrt x ^3 = x * Real.sqrt x := by
        calc
          Real.sqrt x ^3 = Real.sqrt x ^2 * Real.sqrt x := by ring
          _ = x * Real.sqrt x := by rw [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)]
      have h6 : Real.sqrt y ^3 = y * Real.sqrt y := by
        calc
          Real.sqrt y ^3 = Real.sqrt y ^2 * Real.sqrt y := by ring
          _ = y * Real.sqrt y := by rw [Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)]
      rw [h4, h5, h6]
      ring_nf
      <;> field_simp [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith)]
      <;> ring_nf <;> norm_num
      all_goals positivity

    rw [eq2, eq3]
    field_simp [(show x * Real.sqrt x + y * Real.sqrt y ≠ 0 by positivity), hx01]
    <;> ring_nf <;> field_simp [h1, Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith), mul_pos (show 0 < x by linarith) (show 0 < y by linarith)]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg (x * y), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg (x * y), sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x ^2 - y), sq_nonneg (Real.sqrt y ^2 - x)]

  linarith [eq1]