import Mathlib

theorem algebra_195390 :
    IsGreatest {x | ∃ a b c d : ℝ, a ∈ Set.Icc (-6) 6 ∧ b ∈ Set.Icc (-6) 6 ∧ c ∈ Set.Icc (-6) 6 ∧ d ∈ Set.Icc (-6) 6 ∧ x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a} 156 := by
  constructor
  · -- Show that 156 is in the set
    use -6, 6, -6, 6
    constructor
    · -- Show a ∈ [-6, 6]
      norm_num [Set.mem_Icc]
    constructor
    · -- Show b ∈ [-6, 6]
      norm_num [Set.mem_Icc]
    constructor
    · -- Show c ∈ [-6, 6]
      norm_num [Set.mem_Icc]
    constructor
    · -- Show d ∈ [-6, 6]
      norm_num [Set.mem_Icc]
    norm_num -- verify the equality
  · -- Show that 156 is an upper bound
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, hx⟩
    have ha1 : -6 ≤ a := by
      have h1 : a ∈ Set.Icc (-6 : ℝ) 6 := ha
      simp at h1 ⊢
      all_goals linarith
    have h2 : a ≤ 6 := by
      have h2 : a ∈ Set.Icc (-6 : ℝ) 6 := ha
      simp at h2 ⊢
      all_goals linarith
    have h3 : -6 ≤ b := by
      have h3 : b ∈ Set.Icc (-6 : ℝ) 6 := hb
      simp at h3 ⊢
      all_goals linarith
    have h4 : b ≤ 6 := by
      have h4 : b ∈ Set.Icc (-6 : ℝ) 6 := hb
      simp at h4 ⊢
      all_goals linarith
    have h5 : -6 ≤ c := by
      have h5 : c ∈ Set.Icc (-6 : ℝ) 6 := hc
      simp at h5 ⊢
      all_goals linarith
    have h6 : c ≤ 6 := by
      have h6 : c ∈ Set.Icc (-6 : ℝ) 6 := hc
      simp at h6 ⊢
      all_goals linarith
    have h7 : -6 ≤ d := by
      have h7 : d ∈ Set.Icc (-6 : ℝ) 6 := hd
      simp at h7 ⊢
      all_goals linarith
    have h8 : d ≤ 6 := by
      have h8 : d ∈ Set.Icc (-6 : ℝ) 6 := hd
      simp at h8 ⊢
      all_goals linarith
    -- Use nonlinear arithmetic solver to show x ≤ 156
    nlinarith [sq_nonneg (a + 6), sq_nonneg (c + 6), sq_nonneg (b - 6), sq_nonneg (d - 6),
      mul_nonneg (show (0 : ℝ) ≤ 6 - a by linarith) (show (0 : ℝ) ≤ 6 - c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 6 - b by linarith) (show (0 : ℝ) ≤ 6 - d by linarith),
      mul_nonneg (show (0 : ℝ) ≤ a + 6 by linarith) (show (0 : ℝ) ≤ c + 6 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ b + 6 by linarith) (show (0 : ℝ) ≤ d + 6 by linarith)]