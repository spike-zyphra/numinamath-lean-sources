import Mathlib

theorem algebra_258257 (total_votes : ℕ) (h : total_votes ≠ 0) (joao_votes rosa_votes marcos_votes : ℕ)
    (h_joao : joao_votes = (2 / 7 : ℚ) * total_votes) (h_rosa : rosa_votes = (2 / 5 : ℚ) * total_votes)
    (h_marcos : marcos_votes = total_votes - joao_votes - rosa_votes) :
    rosa_votes > joao_votes ∧ rosa_votes > marcos_votes := by 
  have h3 : (total_votes : ℚ) > 0 := by
    have hne : total_votes ≠ 0 := h
    have h35 : total_votes > 0 := by omega
    exact_mod_cast h35
  have h3' : (joao_votes : ℚ) = (2 / 7 : ℚ) * (total_votes : ℚ) := by exact_mod_cast h_joao
  have h4 : (rosa_votes : ℚ) = (2 / 5 : ℚ) * (total_votes : ℚ) := by exact_mod_cast h_rosa
  have h5 : (rosa_votes : ℚ) > (joao_votes : ℚ) := by
    rw [h4, h3']
    have h6 : (2 / 5 : ℚ) * (total_votes : ℚ) > (2 / 7 : ℚ) * (total_votes : ℚ) := by
      have h7 : (total_votes : ℚ) > 0 := h3
      nlinarith
    linarith
  have h8 : (rosa_votes : ℚ) > (joao_votes : ℚ) := h5
  have h9 : rosa_votes > joao_votes := by
    exact_mod_cast h8
  have eq1 : 7 * (joao_votes : ℚ) = 2 * (total_votes : ℚ) := by
    nlinarith [h3']
  have eq2 : 5 * (rosa_votes : ℚ) = 2 * (total_votes : ℚ) := by
    nlinarith [h4]
  have eq3 : 7 * joao_votes = 2 * total_votes := by
    exact_mod_cast eq1
  have eq4 : 5 * rosa_votes = 2 * total_votes := by
    exact_mod_cast eq2
  have h21 : rosa_votes > marcos_votes := by
    have h_eq5 : marcos_votes = total_votes - joao_votes - rosa_votes := h_marcos
    rw [h_eq5] 
    omega
  constructor
  · exact h9
  · exact h21