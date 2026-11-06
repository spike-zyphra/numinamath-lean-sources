import Mathlib

theorem number_theory_230 {x : ℕ} (hx : x ≠ 0) (h : 2013 % x = 0)
    (h1 : ∃ y, 2013 / (x - 5) = y + 2 ∧ ¬∃ z, 2013 / (x - 5) = z - 3) :
    x = 61 := by
  rcases h1 with ⟨y, h_eq, h_ne⟩
  have h2 : ∃ z, 2013 / (x - 5) = z - 3 := by 
    use y + 5
    all_goals
      omega
  have h3 : ¬∃ z, 2013 / (x - 5) = z - 3 := h_ne
  contradiction