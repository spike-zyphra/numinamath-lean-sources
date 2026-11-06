import Mathlib

theorem algebra_109776 :
    IsGreatest {s : ℝ | ∃ a b c : ℝ, s = |a| + |b| + |c| ∧ ∀ x ∈ Set.Icc 0 2, |a * x ^ 2 + b * x + c| ≤ 1} 7 := by
  constructor
  · -- Show 7 is in the set
    use -2, 4, -1
    constructor
    · norm_num [abs_of_pos, abs_of_neg]
    · intro x hx
      have h1 : 0 ≤ x := by
        have h2 : x ∈ Set.Icc (0 : ℝ) 2 := by
          simpa using hx
        exact h2.1
      have h2 : x ≤ 2 := by
        have h3 : x ∈ Set.Icc (0 : ℝ) 2 := by
          simpa using hx
        exact h3.2
      have h5 : -1 ≤ (-2) * x ^ 2 + 4 * x + (-1) := by
        nlinarith [sq_nonneg (x - 1)]
      have h6 : (-2) * x ^ 2 + 4 * x + (-1) ≤ 1 := by 
        nlinarith [sq_nonneg (x - 1)]
      apply abs_le.mpr
      constructor <;> nlinarith 
  · -- Show no value greater than 7 is in the set
    intro s hs
    rcases hs with ⟨a, b, c, h_eq, h⟩
    have h1 := h 0 (by norm_num)
    have h2 := h 1 (by norm_num)
    have h3 := h 2 (by norm_num)
    have h4 := h (1 / 2) (by norm_num)
    have h5 := h (3 / 2) (by norm_num)
    have h11 : -1 ≤ a * (0:ℝ) ^ 2 + b * (0:ℝ) + c := by
      cases abs_le.mp h1 with
      | intro h11 h12 =>
        linarith
    have h12 : a * (0:ℝ) ^ 2 + b * (0:ℝ) + c ≤ 1 := by 
      cases abs_le.mp h1 with
      | intro h11 h12 =>
        linarith
    have h13 : c ≤ 1 := by
      norm_num at h11 h12 ⊢
      all_goals linarith 
    have h14 : -1 ≤ c := by 
      norm_num at h11 h12 ⊢
      all_goals linarith 
    have h21 : -1 ≤ a * (1:ℝ) ^ 2 + b * (1:ℝ) + c := by 
      cases abs_le.mp h2 with
      | intro h21 h22 =>
        linarith 
    have h22 : a * (1:ℝ) ^ 2 + b * (1:ℝ) + c ≤ 1 := by
      cases abs_le.mp h2 with
      | intro h21 h22 =>
        linarith 
    have h31 : -1 ≤ a * (2:ℝ) ^ 2 + b * (2:ℝ) + c := by
      cases abs_le.mp h3 with
      | intro h31 h32 =>
        linarith 
    have h32 : a * (2:ℝ) ^ 2 + b * (2:ℝ) + c ≤ 1 := by
      cases abs_le.mp h3 with
      | intro h31 h32 =>
        linarith 
    have h41 : -1 ≤ a * (1 / 2:ℝ) ^ 2 + b * (1 / 2:ℝ) + c := by 
      cases abs_le.mp h4 with
      | intro h41 h42 =>
        linarith 
    have h42 : a * (1 / 2:ℝ) ^ 2 + b * (1 / 2:ℝ) + c ≤ 1 := by
      cases abs_le.mp h4 with
      | intro h41 h42 =>
        linarith 
    have h51 : -1 ≤ a * (3 / 2:ℝ) ^ 2 + b * (3 / 2:ℝ) + c := by
      cases abs_le.mp h5 with
      | intro h51 h52 =>
        linarith 
    have h52 : a * (3 / 2:ℝ) ^ 2 + b * (3 / 2:ℝ) + c ≤ 1 := by 
      cases abs_le.mp h5 with
      | intro h51 h52 =>
        linarith 
    cases' abs_cases a with ha ha <;> 
      cases' abs_cases b with hb hb <;> 
        cases' abs_cases c with hc4 hc4 <;> 
          all_goals 
            linarith