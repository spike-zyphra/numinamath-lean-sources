import Mathlib

theorem algebra_156078 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h1 : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ 1) (h2 : |f 2| ≥ 7) :
    f = (fun x => 2 * x ^ 2 - 1) ∨ f = (fun x => -2 * x ^ 2 + 1) := by
  rcases hf with ⟨a, b, c, h_def⟩
  have h11 := h1 (-1) (Set.left_mem_Icc.2 (by norm_num))
  have h12 := h1 1 (Set.right_mem_Icc.2 (by norm_num))
  have h13 := h1 0 (by norm_num)
  have h14 := h1 (1 / 2) (by norm_num)
  have h15 := h1 (-1 / 2) (by norm_num)
  simp [h_def] at h11 h12 h13 h14 h15
  have h2' : |f 2| ≥ 7 := h2
  have h21 : |f 2| = |a * (2:ℝ) ^ 2 + b * (2:ℝ) + c| := by
    simp [h_def]
  rw [h21] at h2'
  have h111 : -1 ≤ a - b + c := by
    linarith [abs_le.mp h11]
  have h112 : a - b + c ≤ 1 := by 
    linarith [abs_le.mp h11]
  have h121 : -1 ≤ a + b + c := by 
    linarith [abs_le.mp h12]
  have h122 : a + b + c ≤ 1 := by 
    linarith [abs_le.mp h12]
  have h131 : -1 ≤ c := by
    linarith [abs_le.mp h13]
  have h132 : c ≤ 1 := by
    linarith [abs_le.mp h13]
  have h141 : -1 ≤ a * (1 / 2) ^ 2 + b * (1 / 2) + c := by 
    linarith [abs_le.mp h14]
  have h142 : a * (1 / 2) ^ 2 + b * (1 / 2) + c ≤ 1 := by 
    linarith [abs_le.mp h14]
  have h151 : -1 ≤ a * (-1 / 2) ^ 2 + b * (-1 / 2) + c := by 
    linarith [abs_le.mp h15]
  have h152 : a * (-1 / 2) ^ 2 + b * (-1 / 2) + c ≤ 1 := by
    linarith [abs_le.mp h15]
  have h141' : -1 ≤ a / 4 + b / 2 + c := by
    nlinarith
  have h142' : a / 4 + b / 2 + c ≤ 1 := by
    nlinarith
  have h151' : -1 ≤ a / 4 - b / 2 + c := by
    nlinarith
  have h152' : a / 4 - b / 2 + c ≤ 1 := by
    nlinarith
  cases' abs_choice (a * (2:ℝ) ^ 2 + b * (2:ℝ) + c) with h h
  · -- Case 1: f(2) ≥ 7
    have h22 : a * 4 + b * 2 + c ≥ 7 := by linarith
    have ha1 : a = 2 := by
      nlinarith
    have hb1 : b = 0 := by
      nlinarith
    have hc1 : c = -1 := by
      nlinarith
    left
    funext x
    simp [h_def, ha1, hb1, hc1]
    all_goals linarith
  · -- Case 2: f(2) ≤ -7
    have h22 : a * 4 + b * 2 + c ≤ -7 := by linarith
    have ha2 : a = -2 := by
      nlinarith
    have hb2 : b = 0 := by
      nlinarith
    have hc2 : c = 1 := by
      nlinarith
    right
    funext x
    simp [h_def, ha2, hb2, hc2]
    all_goals linarith