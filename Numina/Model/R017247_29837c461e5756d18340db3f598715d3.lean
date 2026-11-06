import Mathlib

theorem algebra_11633 (f : ℝ → ℝ) (m n : ℝ) (hf : f = fun x => x ^ 2 + m * x + n)
    (h : ∀ x ∈ Set.Icc 1 5, |f x| ≤ 2) :
    m = -6 ∧ n = 7 := by
  have h1 := h 1 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h5 := h 5 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h2 := h 2 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h3 := h 3 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have h4 := h 4 (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  simp [hf] at h1 h2 h3 h4 h5
  have h11 : -2 ≤ (1:ℝ) + m + n := by
    cases abs_le.mp h1 with
    | intro h11 h12 =>
      linarith
  have h12 : (1:ℝ) + m + n ≤ 2 := by
    cases abs_le.mp h1 with
    | intro h11 h12 =>
      linarith
  -- At x = 2
  have h21 : -2 ≤ (4:ℝ) + 2 * m + n := by
    cases abs_le.mp h2 with
    | intro h21 h22 =>
      linarith 
  have h22 : (4:ℝ) + 2 * m + n ≤ 2 := by
    cases abs_le.mp h2 with
    | intro h21 h22 =>
      linarith 
  -- At x = 3
  have h31 : -2 ≤ (9:ℝ) + 3 * m + n := by
    cases abs_le.mp h3 with
    | intro h31 h32 =>
      linarith 
  have h32 : (9:ℝ) + 3 * m + n ≤ 2 := by
    cases abs_le.mp h3 with
    | intro h31 h32 =>
      linarith 
  -- At x = 4
  have h41 : -2 ≤ (16:ℝ) + 4 * m + n := by
    cases abs_le.mp h4 with
    | intro h41 h42 =>
      linarith 
  have h42 : (16:ℝ) + 4 * m + n ≤ 2 := by
    cases abs_le.mp h4 with
    | intro h41 h42 =>
      linarith 
  -- At x = 5
  have h51 : -2 ≤ (25:ℝ) + 5 * m + n := by
    cases abs_le.mp h5 with
    | intro h51 h52 =>
      linarith 
  have h52 : (25:ℝ) + 5 * m + n ≤ 2 := by
    cases abs_le.mp h5 with
    | intro h51 h52 =>
      linarith 
  -- Solving these inequalities to get m and n
  have h6 : m = -6 := by
    nlinarith
  have h7 : n = 7 := by
    nlinarith
  exact ⟨h6, h7⟩