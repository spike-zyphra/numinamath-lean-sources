import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_258507
  (a b : ℕ → ℝ)
  (h₀ : ∀ n, 0 < a n ∧ 0 < b n)
  (h₁ : ∀ n, a n < b n)
  (h₂ : ∀ n, ∀ x, Real.cos (a n * x) + Real.cos (b n * x) ≥ -1 / n) :
  ∃ L, Tendsto (λ n => a n / b n) atTop (𝓝 L) := by
  have h3 := h₂ 0 (Real.pi / b 0)
  have h4 : 0 < b 0 := by 
    have h := h₀ 0
    linarith
  have h4' : a 0 < b 0 := h₁ 0
  have h6 : 0 < a 0 := by
    have h := h₀ 0
    linarith
  have h5 : b 0 * (Real.pi / b 0) = Real.pi := by 
    field_simp [show b 0 ≠ 0 by linarith]
  have h5' : a 0 * (Real.pi / b 0) = a 0 / b 0 * Real.pi := by
    field_simp [show b 0 ≠ 0 by linarith]
    <;> ring
  have h7 : Real.cos (a 0 * (Real.pi / b 0)) = Real.cos (a 0 / b 0 * Real.pi) := by 
    rw [h5']
  have h8 : Real.cos (b 0 * (Real.pi / b 0)) = -1 := by 
    rw [h5]
    norm_num
  have h9 : Real.cos (a 0 * (Real.pi / b 0)) + Real.cos (b 0 * (Real.pi / b 0)) ≥ 0 := by
    simpa using h3
  have h10 : Real.cos (a 0 / b 0 * Real.pi) ≥ 1 := by 
    linarith [h7, h8, h9]
  have h11 : Real.cos (a 0 / b 0 * Real.pi) = 1 := by
    have h12 : Real.cos (a 0 / b 0 * Real.pi) ≤ 1 := by 
      apply Real.cos_le_one
    linarith 
  have h12 : ∃ k : ℤ, a 0 / b 0 * Real.pi = 2 * Real.pi * k := by 
    rw [Real.cos_eq_one_iff] at h11 
    rcases h11 with ⟨k, hk⟩ 
    refine ⟨k, by nlinarith⟩ 
  rcases h12 with ⟨k, hk⟩ 
  have h13 : (a 0 / b 0) = (2 * k : ℝ) := by
    have hne : b 0 ≠ 0 := by linarith
    have h14 : a 0 / b 0 = (2 * k : ℝ) := by
      have h15 : (a 0 / b 0 * Real.pi) = (2 * Real.pi * (k : ℝ)) := by
        simpa using hk 
      have : a 0 / b 0 = (2 * (k : ℝ) ) := by
        have hne1 : Real.pi ≠ 0 := Real.pi_ne_zero 
        apply (mul_left_inj' hne1).mp 
        linarith 
      linarith 
    linarith 
  have h14 : k < 1 := by 
    by_contra h 
    push_neg at h 
    have hk1 : k ≥ 1 := by omega 
    have hk1' : (k : ℝ) ≥ 1 := by exact_mod_cast hk1 
    have h15 : (a 0 / b 0) = (2 * k : ℝ) := h13 
    have h16 : (a 0 / b 0) ≥ (2 : ℝ) := by 
      nlinarith [hk1'] 
    have h4' : a 0 < b 0 := h₁ 0 
    have h17 : b 0 > 0 := h4 
    have h18 : a 0 > 0 := h6 
    have h19 : a 0 / b 0 < 1 := by 
      apply (div_lt_one (by linarith)).mpr 
      nlinarith 
    have h20 : (a 0 / b 0 : ℝ) < (1 : ℝ) := h19 
    nlinarith 
  have h15 : k ≥ 0 := by 
    by_contra h 
    push_neg at h 
    have hk2 : k ≤ -1 := by omega 
    have hk2' : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hk2 
    have h13' : (a 0 / b 0) = (2 * k : ℝ) := h13 
    have h16 : (a 0 / b 0) ≤ (-2 : ℝ) := by 
      nlinarith [hk2'] 
    have h17 : a 0 > 0 := h6 
    have h18 : b 0 > 0 := h4 
    have h19 : a 0 / b 0 > 0 := by 
      apply div_pos 
      all_goals linarith 
    nlinarith 
  have h16 : k = 0 := by omega 
  have h17 : (a 0 / b 0) = (0 : ℝ) := by 
    rw [h13] 
    rw [h16] 
    norm_num 
  have h18 : a 0 = (0 : ℝ) := by
    have hne : b 0 ≠ 0 := by linarith 
    have h19 : a 0 / b 0 = (0 : ℝ) := h17 
    have : a 0 = (0 : ℝ) := by
      field_simp [hne] at h19 ⊢ 
      all_goals linarith 
    assumption 
  have h19 : a 0 > (0 : ℝ) := by 
    have h := h₀ 0 
    linarith 
  linarith