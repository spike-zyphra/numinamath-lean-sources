import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_107648
  {f : ℝ → ℝ}
  (hf1 : ∀ x ∈ Set.Ioo 0 1, f x > 0)
  (hf2 : ∀ x y : ℝ, x ∈ Set.Ioo 0 1 → y ∈ Set.Ioo 0 1 →
    f x / f y + f (1 - x) / f (1 - y) ≤ 2) :
  ∃ c, ∀ x ∈ Set.Ioo 0 1, f x = c := by
  have h1 : ∀ x ∈ Set.Ioo 0 1, f x = f (1 - x) := by
    intro x hx
    have hx1 : x ∈ Set.Ioo 0 1 := hx
    have hx2 : 1 - x ∈ Set.Ioo 0 1 := by
      rw [Set.mem_Ioo] at *
      rcases hx1 with ⟨hx1l, hx1u⟩
      constructor
      · linarith
      · linarith
    have h_ineq := hf2 x (1 - x) hx (show 1 - x ∈ Set.Ioo 0 1 by assumption)
    have hx3 : f x > 0 := hf1 x hx
    have hx4 : f (1 - x) > 0 := hf1 (1 - x) (show 1 - x ∈ Set.Ioo 0 1 by assumption)
    have h2 : f x / f (1 - x) + f (1 - x) / f x ≤ 2 := by
      simpa using h_ineq
    have h3 : f x / f (1 - x) + f (1 - x) / f x = (f x ^ 2 + f (1 - x) ^ 2) / (f x * f (1 - x)) := by
      field_simp [hx4, hx3]
      <;> ring
    rw [h3] at h2
    have h4 : f x ^ 2 + f (1 - x) ^ 2 ≤ 2 * (f x * f (1 - x)) := by
      have hx5 : f x * f (1 - x) > 0 := mul_pos hx3 hx4
      have hx6 : (f x ^ 2 + f (1 - x) ^ 2) / (f x * f (1 - x)) ≤ 2 := h2
      apply (div_le_iff₀ (by linarith)).mp at hx6
      linarith
    have h5 : (f x - f (1 - x)) ^ 2 ≤ 0 := by
      nlinarith [h4]
    have h6 : f x - f (1 - x) = 0 := by nlinarith [sq_nonneg (f x - f (1 - x)), h5]
    linarith
  use f 0.5
  intro x hx
  have hx1 : x ∈ Set.Ioo 0 1 := hx
  have hx2 : (0.5 : ℝ) ∈ Set.Ioo 0 1 := by
    constructor <;> norm_num
  have hx3 : f x > 0 := hf1 x hx
  have hx4 : f 0.5 > 0 := hf1 0.5 (by norm_num)
  have h2_1 := hf2 x 0.5 hx (show (0.5 : ℝ) ∈ Set.Ioo 0 1 by norm_num)
  have h6 : f (1 - (0.5 : ℝ)) = f 0.5 := by
    ring_nf
  have h7 : f x / f 0.5 + f (1 - x) / f 0.5 ≤ 2 := by
    rw [h6] at h2_1
    linarith
  have h8 : f (1 - x) = f x := by
    specialize h1 x hx
    linarith
  rw [h8] at h7
  have h9 : f x ≤ f 0.5 := by
    have hx10 : f x / f 0.5 + f x / f 0.5 ≤ 2 := h7
    have hx11 : f x / f 0.5 + f x / f 0.5 = 2 * (f x / f 0.5) := by ring
    rw [hx11] at hx10
    have hx12 : f x / f 0.5 ≤ 1 := by linarith
    have hx13 : f 0.5 > 0 := hx4
    have hx14 : f x ≤ f 0.5 := by
      apply (div_le_one (by linarith)).mp at hx12
      nlinarith
    linarith
  have h10 : f 0.5 ≤ f x := by
    have h8 : f 0.5 / f x + f (1 - (0.5 : ℝ)) / f (1 - x) ≤ 2 := by
      apply hf2 0.5 x (show (0.5 : ℝ) ∈ Set.Ioo 0 1 by norm_num) hx
    have h11 : f (1 - (0.5 : ℝ)) = f 0.5 := by
      ring_nf
    have h12 : f (1 - x) = f x := by
      specialize h1 x hx
      linarith
    rw [h11, h12] at h8
    have h13 : f 0.5 / f x + f 0.5 / f x ≤ 2 := h8
    have h14 : f 0.5 / f x + f 0.5 / f x = 2 * (f 0.5 / f x) := by ring
    have h15 : f 0.5 / f x ≤ 1 := by
      linarith [h13, h14]
    have hx15 : f x > 0 := hx3
    have hx16 : f 0.5 ≤ f x := by
      apply (div_le_one (by linarith)).mp at h15
      nlinarith
    linarith
  linarith