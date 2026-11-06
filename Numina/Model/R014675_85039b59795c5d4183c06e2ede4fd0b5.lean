import Mathlib

theorem algebra_260104 (a b c d : ℝ) (f g : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ 1)
    (hg : ∀ x ∈ Set.Icc (-1) 1, |g x| ≤ 1)
    (h₀ : ∀ x, f x = 3 * x - a * x ^ 3)
    (h₁ : ∀ x, g x = b + 3 * x + c * x ^ 2 + d * x ^ 3) :
    a = 4 ∧ b = 0 ∧ c = 0 ∧ d = -4 := by

  have h2 := hf 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₀] at h2
  have h3 := hf (-1) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₀] at h3
  have h4 := hf ((1 : ℝ) / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₀] at h4
  have h6 := hf ((-1 : ℝ) / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₀] at h6
  
  have ha1 : a = 4 := by
    norm_num [abs_le] at h2 h3 h4 h6
    nlinarith

  have hb1 := hg 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₁] at hb1

  have hb2 := hg 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₁] at hb2

  have hb3 := hg (-1) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₁] at hb3

  have hb4 := hg ((1 : ℝ) / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₁] at hb4

  have hb5 := hg ((-1 : ℝ) / 2) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  rw [h₁] at hb5

  have hb11 : b = 0 := by
    norm_num [abs_le] at hb1 hb2 hb3 hb4 hb5
    nlinarith

  have hc1 : c = 0 := by
    norm_num [abs_le] at hb1 hb2 hb3 hb4 hb5
    nlinarith

  have hd1 : d = -4 := by
    norm_num [abs_le] at hb1 hb2 hb3 hb4 hb5
    nlinarith
  
  exact ⟨ha1, hb11, hc1, hd1⟩