import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_127509 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = 5 / x + y)
  (M N : ℝ)
  (h₁ : ∃ x y, 1 ≤ x ∧ x ≤ y ∧ y ≤ 5 ∧ f x y = M)
  (h₂ : ∃ x y, 1 ≤ x ∧ x ≤ y ∧ y ≤ 5 ∧ f x y = N)
  (h₃ : ∀ x y, 1 ≤ x ∧ x ≤ y ∧ y ≤ 5 → f x y ≤ M)
  (h₄ : ∀ x y, 1 ≤ x ∧ x ≤ y ∧ y ≤ 5 → f x y ≥ N) :
  M * N = 20 * sqrt 5 := by

  have h5 : f 1 5 = 10 := by
    rw [h₀]
    norm_num

  have h6 : M ≥ 10 := by
    have h5' : f 1 5 ≤ M := h₃ 1 5 (by norm_num)
    linarith [h5, h5']

  have h7 : M ≤ 10 := by
    rcases h₁ with ⟨x, y, hxy1, hxy2, hxy3, heq⟩
    have h9 : 1 ≤ x := hxy1
    have h10 : x ≤ y := hxy2
    have h11 : y ≤ 5 := hxy3
    have h12 : f x y = M := heq
    rw [h₀ x y] at h12
    have h13 : 5 / x + y ≤ 10 := by
      have hx1' : 0 < x := by
        nlinarith
      have h20 : 5 / x ≤ 5 := by
        apply (div_le_iff₀ hx1').mpr
        nlinarith
      have h11' : y ≤ 5 := h11
      linarith
    nlinarith [h12, h13]

  have h8 : M = 10 := by
    linarith

  -- Show $N = 2 \sqrt{5}$

  have h9 : f (Real.sqrt 5) (Real.sqrt 5) = 2 * Real.sqrt 5 := by 
    rw [h₀]
    have h4 : Real.sqrt 5 > 0 := by positivity
    field_simp [h4]
    <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

  -- Show that $N \leq 2 \sqrt{5}$

  have h9' : N ≤ 2 * Real.sqrt 5 := by
    have h9'' : f (Real.sqrt 5) (Real.sqrt 5) ≥ N := h₄ (Real.sqrt 5) (Real.sqrt 5) (by
      constructor
      · -- Show 1 ≤ Real.sqrt 5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), show (1 : ℝ) ^ 2 < (5 : ℝ) by norm_num]
      constructor
      · -- Show Real.sqrt 5 ≤ Real.sqrt 5
        nlinarith
      · -- Show Real.sqrt 5 ≤ 5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    )
    nlinarith [h9, h9'']

  -- Show that $N \geq 2 \sqrt{5}$

  rcases h₂ with ⟨x, y, hx1, hxy, hy5, heq⟩
  have h14 : 1 ≤ x := hx1
  have h15 : x ≤ y := hxy
  have h16 : y ≤ 5 := hy5
  have h17 : f x y = N := heq
  rw [h₀ x y] at h17

  have h18 : 5 / x + y ≥ 2 * Real.sqrt 5 := by 
    have h18 : x + 5 / x ≥ 2 * Real.sqrt 5 := by
      have hx2_pos : x > 0 := by nlinarith
      have h24 : x ^ 2 + 5 - 2 * x * Real.sqrt 5 ≥ 0 := by
        nlinarith [ sq_nonneg (x - Real.sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]
      have h23 : x + 5 / x - 2 * Real.sqrt 5 = (x ^ 2 + 5 - 2 * x * Real.sqrt 5) / x := by
        field_simp
        <;> ring
      have h25 : (x ^ 2 + 5 - 2 * x * Real.sqrt 5) / x ≥ 0 := by
        apply div_nonneg
        · nlinarith
        · positivity
      linarith [h23, h25]
    have h35 : 5 / x + y ≥ x + 5 / x := by
      have h32 : x > 0 := by nlinarith
      have h33 : y ≥ x := by linarith
      have h53 : 5 / x > 0 := by positivity
      have h54 : y ≥ x := by linarith
      nlinarith
    linarith

  have h19 : N ≥ 2 * Real.sqrt 5 := by
    linarith [h17, h18]

  -- Conclude that $N = 2 \sqrt{5}$

  have h20 : N = 2 * Real.sqrt 5 := by 
    linarith

  -- Calculate the product M * N

  rw [h8, h20]
  all_goals
    nlinarith