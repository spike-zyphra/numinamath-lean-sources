import Mathlib

theorem algebra_315969 (x : ℝ) (h : x ∈ Set.Icc 0 9) (h' : (9 - 2) * 91 = ∑ i ∈ Finset.range 7, x + ∑ i ∈ Finset.range 7, (9 - i)) :
    (7 * 91 - x) ^ 2 / 6 = 36 / 7 := by
  have hx0 : 0 ≤ x := by
    have h1 : x ≥ 0 := by
      have h2 : x ∈ Set.Icc (0 : ℝ) 9 := h
      exact h2.1
    linarith
  have hx9 : x ≤ 9 := by
    have h1 : x ≤ 9 := by
      have h2 : x ∈ Set.Icc (0 : ℝ) 9 := h
      exact h2.2
    linarith
  have eq1 : (↑(∑ i in Finset.range 7, (9 - i)) : ℝ) = (42 : ℝ) := by 
    norm_num [Finset.sum_range_succ]
  have eq2 : (∑ i in Finset.range 7, x) = (7 * x : ℝ) := by 
    simp [Finset.sum_const, Finset.card_range]
    all_goals linarith
  have eq3 : (9 - 2 : ℝ) * 91 = (∑ i in Finset.range 7, x) + (↑(∑ i in Finset.range 7, (9 - i)) : ℝ) := by 
    simpa using h'
  rw [eq1] at eq3
  rw [eq2] at eq3
  have eq4 : x = (85 : ℝ) := by 
    norm_num at eq3 
    linarith 
  -- We have hx9 : x ≤ 9 and eq4 : x = 85
  -- Substitute eq4 into hx9 to get contradiction
  have eq5 : (x : ℝ) ≤ (9 : ℝ) := by
    linarith 
  rw [eq4] at eq5 
  all_goals linarith