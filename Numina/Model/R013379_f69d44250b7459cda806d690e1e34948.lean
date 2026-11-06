import Mathlib

theorem number_theory_283466 : IsGreatest {x | ¬∃ a b, x = 3*a + 5*b} 7 := by
  constructor
  · -- Show 7 is in the set
    show ¬∃ a b, (7 = 3 * a + 5 * b)
    rintro ⟨a, b, h⟩
    omega
  · -- Show any element in the set is ≤ 7
    intro x h
    have h1 : ¬∃ a b, x = 3 * a + 5 * b := h
    by_contra h2
    push_neg at h2
    have h3 : x ≥ 8 := by omega
    have h4 : ∃ a b, x = 3 * a + 5 * b := by
      have h5 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
      rcases h5 with (h5 | h5 | h5)
      · -- Case where x % 3 = 0
        use x / 3, 0
        omega
      · -- Case where x % 3 = 1
        have h6 : x % 3 = 1 := h5
        have h8 : x ≥ 10 := by 
          omega
        use (x - 10) / 3, 2
        omega
      · -- Case where x % 3 = 2
        have h6 : x % 3 = 2 := h5
        have h8 : x ≥ 8 := by 
          omega
        use (x - 5) / 3, 1
        omega
    contradiction