import Mathlib

theorem inequalities_310617 (a b : ℝ) (h : ∀ x ∈ Set.Icc 0 1, |a * x + b| ≤ 1) :
    ∀ x ∈ Set.Icc 0 1, |b * x + a| ≤ 2 := by 
  intro x hx
  have hx0 : 0 ≤ x := by
    have h1 : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa using hx
    exact h1.1
  have hx1 : x ≤ 1 := by
    have h1 : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa using hx
    exact h1.2
  have h0 := h 0 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h1 := h 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h2 : -1 ≤ b := by
    linarith [abs_le.mp h0]
  have h3 : b ≤ 1 := by 
    linarith [abs_le.mp h0]
  have h4 : -1 ≤ a + b := by 
    linarith [abs_le.mp h1]
  have h5 : a + b ≤ 1 := by 
    linarith [abs_le.mp h1]
  have hx6 : -2 ≤ b * x + a := by
    nlinarith [abs_le.mp h0, abs_le.mp h1, hx0, hx1]
  have hx7 : b * x + a ≤ 2 := by
    nlinarith [abs_le.mp h0, abs_le.mp h1, hx0, hx1]
  apply abs_le.mpr
  constructor <;> (try linarith)
  all_goals linarith