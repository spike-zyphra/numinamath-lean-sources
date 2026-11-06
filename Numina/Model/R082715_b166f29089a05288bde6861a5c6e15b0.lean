import Mathlib

theorem algebra_170761 :
    IsLeast {x : ℕ | ∃ a b c d e : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0 ∧ a + b + c + d + e = 2018 ∧ x = max (max (a + b) (b + c)) (max (c + d) (d + e))} 673 := by
  constructor
  · -- Show 673 is in the set
    use 672, 1, 672, 1, 672
    all_goals norm_num
  · -- Show the minimality: If x is in the set, then x ≥ 673
    intro x hx
    rcases hx with ⟨a, b, c, d, e, ha, hb, hc, hd, he, heq, hx⟩
    by_contra h
    push_neg at h
    have h1 : max (max (a + b) (b + c)) (max (c + d) (d + e)) < 673 := by
      linarith
    have h2 : a + b < 673 := by
      have h4 : max (max (a + b) (b + c)) (max (c + d) (d + e)) ≥ a + b := by
        simp [max_le_iff]
      linarith
    have h3 : b + c < 673 := by
      have h4 : max (max (a + b) (b + c)) (max (c + d) (d + e)) ≥ b + c := by
        simp [max_le_iff]
      linarith
    have h4 : c + d < 673 := by
      have h5 : max (max (a + b) (b + c)) (max (c + d) (d + e)) ≥ c + d := by
        simp [max_le_iff]
      linarith
    have h5 : d + e < 673 := by
      have h6 : max (max (a + b) (b + c)) (max (c + d) (d + e)) ≥ d + e := by
        simp [max_le_iff]
      linarith
    omega