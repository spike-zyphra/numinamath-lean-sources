import Mathlib

theorem algebra_250144 :
    IsGreatest {s : ℝ | ∃ a b c : ℝ, s = |a| + |b| + |c| ∧ ∀ x ∈ Set.Icc (-1) 1, |a * x ^ 2 + b * x + c| ≤ 1} 3 := by
  constructor
  · -- Show 3 is in the set
    use 2, 0, -1
    constructor
    · -- Show |2| + |0| + |-1| = 3
      norm_num [abs]
    · -- Show that |2 * x^2 + 0 * x - 1| ≤ 1 for all x in [-1, 1]
      intro x hx
      have hx1 : -1 ≤ x := by
        have h_mem : x ∈ Set.Icc (-1) 1 := hx
        exact h_mem.1
      have hx2 : x ≤ 1 := by
        have h_mem : x ∈ Set.Icc (-1) 1 := hx
        exact h_mem.2
      have h1 : -1 ≤ x ^ 2 := by
        nlinarith
      have h2 : x ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
      have h3 : -1 ≤ 2 * x ^ 2 - 1 := by
        nlinarith [sq_nonneg (x)]
      have h4 : 2 * x ^ 2 - 1 ≤ 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
      have h5 : -1 ≤ (2 * x ^ 2 + (0 : ℝ) * x + (-1 : ℝ)) := by
        nlinarith [sq_nonneg (x)]
      have h6 : (2 * x ^ 2 + (0 : ℝ) * x + (-1 : ℝ)) ≤ 1 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
      rw [show (2 : ℝ) * x ^ 2 + (0 : ℝ) * x + (-1 : ℝ) = 2 * x ^ 2 - 1 by ring]
      apply abs_le.mpr
      constructor <;> linarith
  · -- Show 3 is greatest
    intro s hs
    rcases hs with ⟨a, b, c, hs_val, h⟩
    have h1 := h (-1) (Set.left_mem_Icc.mpr (by norm_num))
    have h2 := h 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
    have h3 := h 1 (Set.right_mem_Icc.mpr (by norm_num))
    have h1' : |a * (-1) ^ 2 + b * (-1) + c| ≤ 1 := h1
    have h3' : |a * 1 ^ 2 + b * 1 + c| ≤ 1 := h3
    have h2' : |a * (0 : ℝ) ^ 2 + b * (0 : ℝ) + c| ≤ 1 := h2
    have h11 : |a - b + c| ≤ 1 := by
      have h_eq : a * (-1) ^ 2 + b * (-1) + c = a - b + c := by ring
      rw [h_eq] at h1'
      linarith
    have h13 : |a + b + c| ≤ 1 := by
      have h_eq : a * 1 ^ 2 + b * 1 + c = a + b + c := by ring
      rw [h_eq] at h3'
      linarith
    have h12 : |c| ≤ 1 := by
      have h_eq : a * (0 : ℝ) ^ 2 + b * (0 : ℝ) + c = c := by ring
      rw [h_eq] at h2'
      linarith
    cases' abs_cases a with ha1 ha1 <;> 
      cases' abs_cases b with hb1 hb1 <;> 
        cases' abs_cases c with hc1 hc1 <;> 
          cases' abs_le.mp h11 with h111 h112 <;> 
            cases' abs_le.mp h13 with h131 h132 <;> 
              cases' abs_le.mp h12 with h121 h122 <;> 
                linarith