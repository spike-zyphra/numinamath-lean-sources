import Mathlib

theorem algebra_2634
    (a b c : ℚ)
    (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (a - b) / (b - c) > 0 ∧ (b - c) / (c - a) < 0 ∧ (c - a) / (a - b) < 0 ∨
    (a - b) / (b - c) < 0 ∧ (b - c) / (c - a) > 0 ∧ (c - a) / (a - b) < 0 ∨
    (a - b) / (b - c) < 0 ∧ (b - c) / (c - a) < 0 ∧ (c - a) / (a - b) > 0
      := by
  rcases habc with ⟨ha1, ha2, ha3⟩
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha1
    linarith
  have h2 : b - c ≠ 0 := by
    intro h
    apply ha3
    linarith
  have h3 : c - a ≠ 0 := by
    intro h
    apply ha2
    linarith

  by_cases h4 : a > b
  · -- Case a > b
    by_cases h5 : b > c
    · -- Case a > b > c
      have h6 : a - b > 0 := by linarith
      have h7 : b - c > 0 := by linarith
      have h8 : c - a < 0 := by linarith
      have h9 : (a - b) / (b - c) > 0 := by
        apply div_pos
        all_goals linarith
      have h10 : (b - c) / (c - a) < 0 := by
        apply div_neg_of_pos_of_neg
        all_goals linarith
      have h11 : (c - a) / (a - b) < 0 := by
        apply div_neg_of_neg_of_pos
        all_goals linarith
      left
      exact ⟨h9, h10, h11⟩
    · -- Case a > b and b ≤ c
      have h5' : b ≤ c := by linarith
      have hbne : b ≠ c := ha3
      have h5'' : b < c := by
        by_contra h
        push_neg at h
        have : b = c := by linarith
        tauto
      by_cases h6 : a > c
      · -- Case a > c > b
        have h7 : a - b > 0 := by linarith
        have h8 : b - c < 0 := by linarith
        have h9 : c - a < 0 := by linarith
        have h10 : (a - b) / (b - c) < 0 := by
          apply div_neg_of_pos_of_neg
          all_goals linarith
        have h11 : (b - c) / (c - a) > 0 := by
          apply div_pos_of_neg_of_neg
          all_goals linarith
        have h12 : (c - a) / (a - b) < 0 := by
          apply div_neg_of_neg_of_pos
          all_goals linarith
        right
        left
        exact ⟨h10, h11, h12⟩
      · -- Case a ≤ c. Since a ≠ c, a < c.
        have h6' : a < c := by
          by_contra h
          push_neg at h
          have : a = c := by linarith
          tauto
        have h7 : a - b > 0 := by linarith
        have h8 : b - c < 0 := by linarith
        have h9 : c - a > 0 := by linarith
        have h10 : (a - b) / (b - c) < 0 := by
          apply div_neg_of_pos_of_neg
          all_goals linarith
        have h11 : (b - c) / (c - a) < 0 := by
          apply div_neg_of_neg_of_pos
          all_goals linarith
        have h12 : (c - a) / (a - b) > 0 := by
          apply div_pos
          all_goals linarith
        right
        right
        exact ⟨h10, h11, h12⟩
  · -- Case a ≤ b. Since a ≠ b, a < b.
    have h4' : a < b := by
      by_contra h
      push_neg at h
      have : a = b := by linarith
      tauto
    by_cases h5 : b > c
    · -- Case a < b > c
      by_cases h6 : a > c
      · -- Case a > c < b
        have h7 : a - b < 0 := by linarith
        have h8 : b - c > 0 := by linarith
        have h9 : c - a < 0 := by linarith
        have h10 : (a - b) / (b - c) < 0 := by
          apply div_neg_of_neg_of_pos
          all_goals linarith
        have h11 : (b - c) / (c - a) < 0 := by
          apply div_neg_of_pos_of_neg
          all_goals linarith
        have h12 : (c - a) / (a - b) > 0 := by
          apply div_pos_of_neg_of_neg
          all_goals linarith
        right
        right
        exact ⟨h10, h11, h12⟩
      · -- Case a ≤ c. Since a ≠ c, a < c.
        have h6' : a < c := by
          by_contra h
          push_neg at h
          have : a = c := by linarith
          tauto
        have h7 : a - b < 0 := by linarith
        have h8 : b - c > 0 := by linarith
        have h9 : c - a > 0 := by linarith
        have h10 : (a - b) / (b - c) < 0 := by
          apply div_neg_of_neg_of_pos
          all_goals linarith
        have h11 : (b - c) / (c - a) > 0 := by
          apply div_pos
          all_goals linarith
        have h12 : (c - a) / (a - b) < 0 := by
          apply div_neg_of_pos_of_neg
          all_goals linarith
        right
        left
        exact ⟨h10, h11, h12⟩
    · -- Case a < b and b ≤ c
      have h5' : b ≤ c := by linarith
      have hbne : b ≠ c := ha3
      have h5'' : b < c := by
        by_contra h
        push_neg at h
        have : b = c := by linarith
        tauto
      have h6 : a - b < 0 := by linarith
      have h7 : b - c < 0 := by linarith
      have h8 : c - a > 0 := by
        nlinarith
      have h9 : (a - b) / (b - c) > 0 := by
        apply div_pos_of_neg_of_neg
        all_goals linarith
      have h10 : (b - c) / (c - a) < 0 := by
        apply div_neg_of_neg_of_pos
        all_goals linarith
      have h11 : (c - a) / (a - b) < 0 := by
        apply div_neg_of_pos_of_neg
        all_goals linarith
      left
      exact ⟨h9, h10, h11⟩