import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_219368
  {f : ℝ → ℝ}
  (hf : ∀ x ∈ Set.Ioo 0 1, f x > 0)
  (h : ∀ x y : ℝ, x ∈ Set.Ioo 0 1 → y ∈ Set.Ioo 0 1 →
    f x / f y + f (1 - x) / f (1 - y) ≤ 2) :
  ∃ c, ∀ x ∈ Set.Ioo 0 1, f x = c := by
  have h1 : ∀ x ∈ Set.Ioo 0 1, f x = f (1 - x) := by
    intro x hx
    have h2 : 1 - x ∈ Set.Ioo 0 1 := by
      rw [Set.mem_Ioo] at hx ⊢
      constructor
      · linarith
      · linarith
    have h3 := h x (1 - x) hx h2
    have h4 : 1 - (1 - x) = x := by
      ring
    rw [h4] at h3
    have h5 : f x > 0 := hf x hx
    have h6 : f (1 - x) > 0 := hf (1 - x) h2
    have h7 : f x ^ 2 + f (1 - x) ^ 2 - 2 * (f x * f (1 - x)) ≤ 0 := by
      have h8 : f x * f (1 - x) > 0 := mul_pos h5 h6 
      have h9 : f x / f (1 - x) + f (1 - x) / f x - 2 ≤ 0 := by linarith 
      have h10 : (f x * f (1 - x)) * (f x / f (1 - x) + f (1 - x) / f x - 2) ≤ 0 := by 
        nlinarith 
      have h11 : (f x * f (1 - x)) * (f x / f (1 - x) + f (1 - x) / f x - 2) = f x ^ 2 + f (1 - x) ^ 2 - 2 * (f x * f (1 - x)) := by
        field_simp [h6, h5]
        <;> ring 
      linarith [h11, h10]
    nlinarith [sq_nonneg (f x - f (1 - x)), h7]
  use f (1 / 2)
  intro x hx
  have h2 : ∀ x ∈ Set.Ioo 0 1, ∀ y ∈ Set.Ioo 0 1, f x ≤ f y := by
    intro x hx y hy
    have hxy := h x y hx hy
    have hfx1 : f x = f (1 - x) := h1 x hx 
    have hfy1 : f y = f (1 - y) := h1 y hy 
    have h6 : 1 - x ∈ Set.Ioo 0 1 := by 
      apply Set.mem_Ioo.mpr 
      constructor 
      · linarith [hx.1, hx.2]
      · linarith [hx.1, hx.2]
    have h7 : 1 - y ∈ Set.Ioo 0 1 := by 
      apply Set.mem_Ioo.mpr 
      constructor 
      · linarith [hy.1, hy.2]
      · linarith [hy.1, hy.2]
    have hfx1' : f (1 - x) = f x := by linarith [hfx1] 
    have hfy1' : f (1 - y) = f y := by linarith [hfy1] 
    rw [show f (1 - x) = f x by linarith [hfx1'], show f (1 - y) = f y by linarith [hfy1']] at hxy 
    have h9 : f y > 0 := hf y hy 
    have h10 : f x / f y + f x / f y ≤ 2 := by nlinarith 
    have h4 : f x ≤ f y := by 
      have h5 : f y > 0 := h9
      have h11 : f x / f y ≤ 1 := by 
        nlinarith 
      have h12 : f x ≤ f y := by 
        apply (div_le_one (by positivity)).mp at h11 
        linarith 
      linarith 
    linarith 
  have hxy' := h2 x hx (1 / 2) (by 
    exact ⟨by norm_num, by norm_num⟩
  )
  have h3 := h2 (1 / 2) (by
    exact ⟨by norm_num, by norm_num⟩
  ) x hx 
  linarith [hxy', h3]