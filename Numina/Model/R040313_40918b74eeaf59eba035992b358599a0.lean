import Mathlib

theorem algebra_195320 :
    IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
      a ∈ Set.Icc (-7) 7 ∧ b ∈ Set.Icc (-7) 7 ∧ c ∈ Set.Icc (-7) 7 ∧ d ∈ Set.Icc (-7) 7} 210 := by
  constructor
  · -- First, we need to prove that 210 is in the set
    use -7, 7, -7, 7
    norm_num [Set.mem_Icc]
  · -- Now, prove that 210 is the greatest
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩
    have ha1 : -7 ≤ a := by
      have h : a ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := ha
      exact h.1
    have ha2 : a ≤ 7 := by
      have h : a ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := ha
      exact h.2
    have hb1 : -7 ≤ b := by
      have h : b ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := hb
      exact h.1
    have hb2 : b ≤ 7 := by
      have h : b ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := hb
      exact h.2
    have hc1 : -7 ≤ c := by
      have h : c ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := hc
      exact h.1
    have hc2 : c ≤ 7 := by
      have h : c ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := hc
      exact h.2
    have hd1 : -7 ≤ d := by
      have h : d ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := hd
      exact h.1
    have hd2 : d ≤ 7 := by
      have h : d ∈ Set.Icc (-7 : ℝ) (7 : ℝ) := hd
      exact h.2
    nlinarith [sq_nonneg (a + 7), sq_nonneg (b - 7), sq_nonneg (c + 7), sq_nonneg (d - 7),
      mul_nonneg (show (0 : ℝ) ≤ 7 + a by linarith) (show (0 : ℝ) ≤ 7 - a by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 7 + b by linarith) (show (0 : ℝ) ≤ 7 - b by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 7 + c by linarith) (show (0 : ℝ) ≤ 7 - c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 7 + d by linarith) (show (0 : ℝ) ≤ 7 - d by linarith)
    ]