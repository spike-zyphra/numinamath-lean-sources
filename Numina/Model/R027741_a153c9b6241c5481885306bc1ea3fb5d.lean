import Mathlib

theorem number_theory_6342 : IsGreatest {x | ¬∃ n m, x = 5 * n + 8 * m} 27 := by
  constructor
  · -- Show 27 is in the set {x | ¬∃ n m, x = 5 * n + 8 * m}
    show ¬∃ n m, 27 = 5 * n + 8 * m
    rintro ⟨n, m, h⟩
    have eq1 : 5 * n + 8 * m = 27 := by
      omega
    have h1 : n ≤ 5 := by 
      omega
    have h2 : m ≤ 3 := by 
      omega
    interval_cases n <;> interval_cases m <;> omega
  · -- Show 27 is greatest in the set
    intro x hx
    have h1 : ¬∃ n m, x = 5 * n + 8 * m := hx
    by_contra h2
    push_neg at h2
    have h3 : ∃ n m, x = 5 * n + 8 * m := by
      have h2' : x > 27 := by 
        omega
      have h3 : x > 27 := h2
      have h4 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by 
        omega
      rcases h4 with h4 | h4 | h4 | h4 | h4
      · -- x ≡ 0 [mod5]
        have h5 : ∃ n m, x = 5 * n + 8 * m := by
          use x / 5, 0
          omega
        assumption
      · -- x ≡1 [mod5]
        have h8 : ∃ n m, x = 5 * n + 8 * m :=  by
          have h6 : x % 5 = 1 := h4
          use (x - 16) / 5, 2
          omega
        assumption
      · -- x ≡2 [mod5]
        have h8 : ∃ n m, x = 5 * n + 8 * m :=  by
          have h6 : x % 5 = 2 := h4
          use (x - 32) / 5, 4
          omega
        assumption
      · -- x ≡3 [mod5]
        have h8 : ∃ n m, x = 5 * n + 8 * m :=  by
          have h6 : x % 5 = 3 := h4
          use (x - 8) / 5, 1
          omega
        assumption
      · -- x ≡4 [mod5]
        have h8 : ∃ n m, x = 5 * n + 8 * m := by
          have h6 : x % 5 = 4 := h4
          use (x - 24) / 5, 3
          omega
        assumption
    contradiction