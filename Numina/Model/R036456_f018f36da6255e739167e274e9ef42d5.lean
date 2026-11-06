import Mathlib

theorem algebra_145958 {a b : ℝ} (ha : ∀ x ∈ Set.Icc 0 1, ∀ y ∈ Set.Icc 0 1, |a * x + b + a * y + b - x * y| ≤ 1 / 4) :
    a = 1 / 2 ∧ b = -1 / 8 := by
  have h1 := ha 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h1' : |a * (0 : ℝ) + b + a * (0 : ℝ) + b - (0 : ℝ) * (0 : ℝ)| ≤ 1 / 4 := by
    simpa using h1
  have h1b : -1/8 ≤ b ∧ b ≤ 1/8 := by
    norm_num at h1'
    constructor
    · linarith [abs_le.mp h1']
    · linarith [abs_le.mp h1']
  have h2 := ha 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h2' : |a * (1 : ℝ) + b + a * (1 : ℝ) + b - (1 : ℝ) * (1 : ℝ)| ≤ 1 / 4 := by
    simpa using h2
  have h2ab : 3/8 ≤ a + b ∧ a + b ≤ 5/8 := by
    norm_num at h2'
    constructor
    · linarith [abs_le.mp h2']
    · linarith [abs_le.mp h2']
  have h3 := ha 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h3' : |a * (1 : ℝ) + b + a * (0 : ℝ) + b - (1 : ℝ) * (0 : ℝ)| ≤ 1 / 4 := by
    simpa using h3
  have h3a2b : -1/4 ≤ a + 2 * b ∧ a + 2 * b ≤ 1/4 := by
    norm_num at h3'
    constructor
    · linarith [abs_le.mp h3']
    · linarith [abs_le.mp h3']
  have eq1 : a = 1 / 2 := by
    cases' abs_le.mp h1' with h11 h12
    cases' abs_le.mp h2' with h21 h22
    cases' abs_le.mp h3' with h31 h32
    linarith
  have eq2 : b = -1 / 8 := by
    cases' abs_le.mp h1' with h11 h12
    cases' abs_le.mp h2' with h21 h22
    cases' abs_le.mp h3' with h31 h32
    linarith
  exact ⟨eq1, eq2⟩