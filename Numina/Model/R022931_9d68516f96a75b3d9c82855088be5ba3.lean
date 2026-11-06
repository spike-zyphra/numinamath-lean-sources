import Mathlib

theorem number_theory_2674 :
    ¬(∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ Nat.Coprime a b ∧ Nat.Coprime b c ∧
      (a + c)^2 % b = 0 ∧ a^2 + c^2 % b = 0 ∧ (a + b)^2 % c = 0 ∧ a^2 + b^2 % c = 0) := by
  intro h
  rcases h with ⟨a, b, c, ha, hb, hc, h1, h2, h3, h4, h5, h6⟩
  all_goals
    norm_num at h1 h2 h3 h4 h5 h6
    all_goals
      omega