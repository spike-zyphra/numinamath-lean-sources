import Mathlib.Tactic

theorem number_theory_147555 :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a^4 = b^3 + c^2 :=
  ⟨6, 8, 28, by norm_num⟩