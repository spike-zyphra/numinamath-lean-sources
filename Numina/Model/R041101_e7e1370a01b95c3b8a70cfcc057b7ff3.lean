import Mathlib

theorem algebra_20938 : IsGreatest { (matches_won) | (total_matches : ℕ) (matches_won : ℕ) (h₀ : total_matches > 0) (h₁ : matches_won / total_matches = (0.500 : ℚ)) (h₂ : (matches_won + 3) / (total_matches + 4) > (0.503 : ℚ)) } 164 := by
  constructor
  · -- Show 164 is in the set
    use 328, 164, by norm_num, by norm_num, by norm_num
  · -- Show 164 is greatest
    intro matches_won hw
    rcases hw with ⟨total_matches, matches_won, h₀, h₁, h₂⟩
    by_contra h
    push_neg at h
    -- h₁ : matches_won / total_matches = (0.500 : ℚ)
    have h₃ : (matches_won : ℚ) / (total_matches : ℚ) = (0.500 : ℚ) := by
      simpa using h₁
    -- From win ratio 0.5, we have total_matches = 2 * matches_won
    have h₄ : (total_matches : ℚ) = 2 * (matches_won : ℚ) := by
      field_simp at h₃
      nlinarith
    have h₅ : total_matches = 2 * matches_won := by
      exact_mod_cast h₄
    -- From the complex structure of the set, h₂ is (∃(_ : (match+3)/(total+4) > 0.503), match = match)
    -- We extract the inequality part from h₂ using `obtain`.
    have h2 : (matches_won + 3 : ℚ) / (total_matches + 4 : ℚ) > (0.503 : ℚ) := by
      obtain ⟨h3, _⟩ := h₂ -- h3 is the inequality part, _ is the trivial `matches_won = matches_won`
      simpa using h3
    have h₇ : (total_matches : ℚ) + (4 : ℚ) > (0 : ℚ) := by
      have h₈ : (total_matches : ℚ) > (0 : ℚ) := by
        exact_mod_cast (show 0 < total_matches by linarith)
      nlinarith
    have h₈ : (matches_won + 3 : ℚ) > (0.503 : ℚ) * ((total_matches : ℚ) + (4 : ℚ)) := by
      have h₇_pos : (total_matches : ℚ) + (4 : ℚ) > 0 := h₇
      apply (lt_div_iff₀ h₇_pos).mp at h2
      linarith
    -- Substitute total_matches = 2 * matches_won from h₄ into inequality h₈
    rw [show (total_matches : ℚ) = (2 * (matches_won : ℚ)) by exact_mod_cast h₄] at h₈
    have h₉ : (matches_won : ℚ) < (988 / 6 : ℚ) := by
      norm_num at h₈ ⊢
      nlinarith
    have h₁₀ : matches_won < 165 := by
      by_contra h
      push_neg at h
      have h₁₁ : (matches_won : ℚ) ≥ (165 : ℚ) := by
        exact_mod_cast h
      nlinarith
    omega