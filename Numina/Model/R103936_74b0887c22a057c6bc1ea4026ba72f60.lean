import Mathlib

theorem algebra_124066 (f : ℝ → ℝ) (a b c : ℝ) (hf : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ 1)
    (h₀ : ∀ x, f x = a * x ^ 2 + b * x + c) :
    |a| + |b| + |c| ≤ 3 := by

  have h1 := hf 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h2 := hf (-1) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h3 := hf (0) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h4 := hf (0.5 : ℝ) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h5 := hf (-0.5 : ℝ) (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)

  have h1' : |f 1| ≤ 1 := h1
  have h2' : |f (-1)| ≤ 1 := h2
  have h3' : |f 0| ≤ 1 := h3
  have h4' : |f 0.5| ≤ 1 := h4
  have h5' : |f (-0.5)| ≤ 1 := h5

  have h11 : f 1 = a * 1 ^ 2 + b * 1 + c := h₀ 1
  have h22 : f (-1) = a * (-1) ^ 2 + b * (-1) + c := h₀ (-1)
  have h33 : f 0 = a * (0:ℝ) ^ 2 + b * (0:ℝ) + c := h₀ 0
  have h44 : f 0.5 = a * (0.5:ℝ) ^ 2 + b * (0.5:ℝ) + c := h₀ 0.5
  have h55 : f (-0.5) = a * (-0.5:ℝ) ^ 2 + b * (-0.5:ℝ) + c := h₀ (-0.5)

  rw [h33] at h3'
  have hc1 : -1 ≤ c := by linarith [abs_le.mp h3']
  have hc2 : c ≤ 1 := by linarith [abs_le.mp h3']

  rw [h11] at h1'
  rw [h22] at h2'

  have h11' : -1 ≤ a * (1 : ℝ) ^ 2 + b * (1 : ℝ) + c := by linarith [abs_le.mp h1']
  have h12' : a * (1 : ℝ) ^ 2 + b * (1 : ℝ) + c ≤ 1 := by linarith [abs_le.mp h1']

  have h21' : -1 ≤ a * (-1 : ℝ) ^ 2 + b * (-1 : ℝ) + c := by linarith [abs_le.mp h2']
  have h22' : a * (-1 : ℝ) ^ 2 + b * (-1 : ℝ) + c ≤ 1 := by linarith [abs_le.mp h2']

  rw [h44] at h4'
  rw [h55] at h5'

  have h41' : -1 ≤ a * (0.5 : ℝ) ^ 2 + b * (0.5 : ℝ) + c := by linarith [abs_le.mp h4']
  have h42' : a * (0.5 : ℝ) ^ 2 + b * (0.5 : ℝ) + c ≤ 1 := by linarith [abs_le.mp h4']

  have h51' : -1 ≤ a * (-0.5 : ℝ) ^ 2 + b * (-0.5 : ℝ) + c := by linarith [abs_le.mp h5']
  have h52' : a * (-0.5 : ℝ) ^ 2 + b * (-0.5 : ℝ) + c ≤ 1 := by linarith [abs_le.mp h5']

  cases' abs_cases a with ha ha
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · nlinarith
      · nlinarith
    · cases' abs_cases c with hc hc
      · nlinarith
      · nlinarith
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · nlinarith
      · nlinarith
    · cases' abs_cases c with hc hc
      · nlinarith
      · nlinarith