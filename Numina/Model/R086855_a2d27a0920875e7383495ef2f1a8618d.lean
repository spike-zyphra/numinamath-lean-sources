import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_60367 {a : ℕ → ℝ}
  (ha1 : a 1 = 3 / 2)
  (han : ∀ n, a (n + 1) = (3 * (a n)^2 + 4 * a n - 3) / (4 * (a n)^2)) :
  (∀ n, 1 < a n ∧ a (n + 1) < a n) ∧
  ∃ L, Tendsto (λ n => a n) atTop (𝓝 L) ∧
  Tendsto (λ n => ∏ i ∈ range n, a (i + 1)) atTop (𝓝 1) := by  
  have h0 := han 0
  rw [show (0 + 1 : ℕ) = 1 by omega] at h0
  rw [ha1] at h0
  by_cases h : a 0 = 0
  · rw [h] at h0
    norm_num at h0 <;> linarith
  · have ha0_ne_zero : a 0 ≠ 0 := h
    field_simp [ha0_ne_zero] at h0
    nlinarith [sq_nonneg (a 0 - 1 : ℝ), sq_nonneg (a 0 - 3 / 2 : ℝ), sq_nonneg (a 0 + ( -4 / 3 : ℝ) ) ]