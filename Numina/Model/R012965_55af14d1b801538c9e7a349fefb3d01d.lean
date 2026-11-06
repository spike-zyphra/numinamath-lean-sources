import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_205506 (f : ℝ → ℝ) (hf : f = λ x => x + 9 / x)
  (M m : ℝ) (hM : ∃ x ∈ Icc 1 4, f x = M) (hm : ∃ x ∈ Icc 1 4, f x = m)
  (hMub : ∀ x ∈ Icc 1 4, f x ≤ M) (hmub : ∀ x ∈ Icc 1 4, f x ≥ m) :
  M - m = 4 := by
  have h1 : f 1 = 10 := by
    rw [hf]
    norm_num
  have h3 : f 3 = 6 := by
    rw [hf]
    norm_num
  have h5 : M ≥ 10 := by
    have h1in : (1 : ℝ) ∈ Icc (1 : ℝ) 4 := by
      norm_num [mem_Icc]
    have h6 : f 1 ≤ M := hMub 1 h1in
    linarith [h1, h6]
  have h7 : M ≤ 10 := by
    by_contra h
    push_neg at h
    rcases hM with ⟨x₀, hx₀, hfx₀⟩
    have hx₀1 : 1 ≤ x₀ := by
      have h : x₀ ∈ Icc (1 : ℝ) 4 := hx₀
      exact h.1
    have hx₀2 : x₀ ≤ 4 := by
      have h : x₀ ∈ Icc (1 : ℝ) 4 := hx₀
      exact h.2
    have hx₀3 : x₀ > 0 := by nlinarith
    have hfx0 : f x₀ = x₀ + 9 / x₀ := by
      rw [hf]
    have h11 : x₀ + 9 / x₀ > (10 : ℝ) := by
      linarith [hfx0, hfx₀, h]
    have h12 : x₀ ^ 2 + 9 > 10 * x₀ := by
      have h9 : x₀ > 0 := hx₀3
      have h13 : x₀ + 9 / x₀ > (10 : ℝ) := h11
      have h14 : (x₀ + 9 / x₀) * x₀ > 10 * x₀ := by
        nlinarith [h13, show x₀ > 0 by linarith]
      have h15 : (x₀ + 9 / x₀) * x₀ = x₀ ^ 2 + 9 := by
        field_simp
        <;> nlinarith
      nlinarith [h15, h14]
    have h16 : (x₀ - 1) * (x₀ - 9) > 0 := by
      nlinarith
    have h17 : (x₀ - 1) * (x₀ - 9) ≤ 0 := by
      nlinarith [sq_nonneg (x₀ - 1), sq_nonneg (x₀ - 4), sq_nonneg (x₀ - 3)]
    nlinarith
  have hM10 : M = 10 := by linarith
  -- Show that m ≤ 6
  have h8 : m ≤ 6 := by
    have h9 : 3 ∈ Icc (1 : ℝ) 4 := by
      norm_num [mem_Icc]
    have h10 : f 3 ≥ m := hmub 3 h9
    linarith [h3, h10]
  -- Show that m ≥ 6
  have h9 : m ≥ 6 := by
    by_contra h
    push_neg at h
    rcases hm with ⟨x₀, hx₀, hfx₀⟩
    have hfx₀1 : f x₀ < (6 : ℝ) := by
      linarith [hfx₀, h]
    have hx₀1 : 1 ≤ x₀ := by
      have h : x₀ ∈ Icc (1 : ℝ) 4 := hx₀
      exact h.1
    have hx₀2 : x₀ ≤ 4 := by
      have h : x₀ ∈ Icc (1 : ℝ) 4 := hx₀
      exact h.2
    have hfx0 : f x₀ = x₀ + 9 / x₀ := by
      rw [hf]
    have h11 : x₀ + 9 / x₀ < (6 : ℝ) := by
      nlinarith [hfx0, hfx₀1]
    have hx₀3 : x₀ > 0 := by nlinarith
    have h12 : x₀ ^ 2 + 9 < 6 * x₀ := by
      have h13 : x₀ + 9 / x₀ < (6 : ℝ) := h11
      have h14 : (x₀ + 9 / x₀) * x₀ < 6 * x₀ := by
        nlinarith [h13, show x₀ > 0 by linarith]
      have h15 : (x₀ + 9 / x₀) * x₀ = x₀ ^ 2 + 9 := by
        field_simp
        <;> nlinarith
      nlinarith [h15, h14]
    have h16 : (x₀ - 3) ^ 2 < (0 : ℝ) := by
      nlinarith
    have h17 : (x₀ - 3) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith
  -- Now from M = 10 and m = 6, conclude M-m = 4
  have hm6 : m = 6 := by linarith
  rw [hM10, hm6]
  all_goals norm_num