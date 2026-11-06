import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem inequalities_138732 (f g : ℝ → ℝ) :
  ∃ (x y : ℝ), x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧ |x * y - f x - g y| ≥ 1 / 4 := by
  by_contra h
  push_neg at h
  have h1 : ∀ (x y : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → -1 / 4 < x * y - f x - g y ∧ x * y - f x - g y < 1 / 4 := by
    intro x y hx hy
    have hxy : |x * y - f x - g y| < 1 / 4 := h x y hx hy
    constructor
    · linarith [abs_lt.mp hxy]
    · linarith [abs_lt.mp hxy]
  
  have h11 := h1 0 0 (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  have h12 := h1 0 1 (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  have h13 := h1 1 0 (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  have h14 := h1 1 1 (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  norm_num at h11 h12 h13 h14 
  linarith