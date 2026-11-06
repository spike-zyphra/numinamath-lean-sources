import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_189953 {a : ℝ} (ha : 0 < a)
  (f : ℝ → ℝ) (hf : ∀ x ∈ Icc 0 a, f x = sqrt (a + x) + sqrt (a - x)) :
  StrictAntiOn f (Icc 0 a) := by
  intro x hx y hy hxy
  have hx1 : 0 ≤ x := by
    have h1 : x ∈ Icc (0 : ℝ) a := hx
    exact h1.1
  have hx2 : x ≤ a := by
    have h1 : x ∈ Icc (0 : ℝ) a := hx
    exact h1.2
  have hy1 : 0 ≤ y := by
    have h2 : y ∈ Icc (0 : ℝ) a := hy
    exact h2.1
  have hy2 : y ≤ a := by
    have h2 : y ∈ Icc (0 : ℝ) a := hy
    exact h2.2
  have hfx : f x = sqrt (a + x) + sqrt (a - x) := by
    specialize hf x hx
    simpa using hf
  have hfy : f y = sqrt (a + y) + sqrt (a - y) := by
    specialize hf y hy
    simpa using hf
  rw [hfx, hfy]
  have h1 : a + x ≥ 0 := by
    linarith
  have h2 : a - x ≥ 0 := by
    linarith
  have h3 : a + y ≥ 0 := by
    linarith
  have h4 : a - y ≥ 0 := by
    linarith
  have h5 : sqrt (a + x) + sqrt (a - x) > sqrt (a + y) + sqrt (a - y) := by
    have h6 : (sqrt (a + x) + sqrt (a - x)) ^ 2 > (sqrt (a + y) + sqrt (a - y)) ^ 2 := by
      have h7 : sqrt (a + x) ≥ 0 := Real.sqrt_nonneg (a + x)
      have h8 : sqrt (a - x) ≥ 0 := Real.sqrt_nonneg (a - x)
      have h9 : sqrt (a + y) ≥ 0 := Real.sqrt_nonneg (a + y)
      have h10 : sqrt (a - y) ≥ 0 := Real.sqrt_nonneg (a - y)
      have h11 : (sqrt (a + x) + sqrt (a - x)) ^ 2 = (sqrt (a + x)) ^ 2 + (sqrt (a - x)) ^ 2 + 2 * (sqrt (a + x) * sqrt (a - x)) := by ring
      have h12 : (sqrt (a + y) + sqrt (a - y)) ^ 2 = (sqrt (a + y)) ^ 2 + (sqrt (a - y)) ^ 2 + 2 * (sqrt (a + y) * sqrt (a - y)) := by ring
      have h13 : (sqrt (a + x)) ^ 2 = a + x := by
        rw [Real.sq_sqrt]
        linarith
      have h14 : (sqrt (a - x)) ^ 2 = a - x := by
        rw [Real.sq_sqrt]
        linarith
      have h15 : (sqrt (a + y)) ^ 2 = a + y := by
        rw [Real.sq_sqrt]
        linarith
      have h16 : (sqrt (a - y)) ^ 2 = a - y := by
        rw [Real.sq_sqrt]
        linarith
      have h17 : sqrt (a + x) * sqrt (a - x) = Real.sqrt ((a + x) * (a - x)) := by
        rw [← Real.sqrt_mul (by linarith)]
      have h18 : sqrt (a + y) * sqrt (a - y) = Real.sqrt ((a + y) * (a - y)) := by
        rw [← Real.sqrt_mul (by linarith)]
      have h19 : (a + x) * (a - x) > (a + y) * (a - y) := by
        nlinarith [sq_pos_of_pos ha, sq_nonneg (x - y), sq_pos_of_pos (show 0 < a by linarith), hxy]
      have h21 : Real.sqrt ((a + x) * (a - x)) > Real.sqrt ((a + y) * (a - y)) := by
        apply Real.sqrt_lt_sqrt
        nlinarith
        nlinarith
      nlinarith [Real.sqrt_nonneg ((a + x) * (a - x)), Real.sqrt_nonneg ((a + y) * (a - y)), h21, sq_nonneg (sqrt (a + x) - sqrt (a + y)), sq_nonneg (sqrt (a - x) - sqrt (a - y)), Real.sq_sqrt (show 0 ≤ (a + x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (a - x : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (a + y : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (a - y : ℝ) by linarith)]
    have h110 : sqrt (a + x) + sqrt (a - x) > 0 := by
      nlinarith [Real.sqrt_nonneg (a + x), Real.sqrt_nonneg (a - x), Real.sqrt_pos.mpr (show (0 : ℝ) < a + x by linarith)]
    have h111 : sqrt (a + y) + sqrt (a - y) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (a + y), Real.sqrt_nonneg (a - y)]
    nlinarith [Real.sqrt_nonneg (a + x), Real.sqrt_nonneg (a - x), Real.sqrt_nonneg (a + y), Real.sqrt_nonneg (a - y)]
  exact h5