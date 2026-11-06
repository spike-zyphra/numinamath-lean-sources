import Mathlib

theorem algebra_599519 (a b c : ℝ) (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc 0 1, |f x| ≤ 1) (h : f = fun x => a * x ^ 2 + b * x + c) :
    |a| + |b| + |c| ≤ 17 := by

  have h1 := hf 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [h] at h1

  have h2 := hf 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [h] at h2

  have h3 := hf (1 / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [h] at h3

  have h4 := hf (2 / 3) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [h] at h4

  have h5 := hf (1 / 3) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [h] at h5

  cases' abs_cases a with ha1 ha1 <;> cases' abs_cases b with hb1 hb1 <;> cases' abs_cases c with hc1 hc1 <;> 
    linarith [abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5]