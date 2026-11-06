import Mathlib

theorem number_theory_99825 : IsGreatest {x | ¬∃ a b c, x = 5*a + 8*b + 12*c} 19 := by
  constructor
  · -- Show 19 is in the set
    show ¬∃ a b c, 19 = 5*a + 8*b + 12*c
    rintro ⟨a, b, c, h⟩
    omega
  · -- Show that 19 is greatest in the set
    intro x hx
    have h : ¬∃ a b c, x = 5*a + 8*b + 12*c := hx
    by_contra h1
    push_neg at h1
    have h2 : x > 19 := h1
    have h3 : ∃ a b c, x = 5*a + 8*b + 12*c := by
      have h4 : x ≥ 20 := by
        omega
      have h5 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
        omega
      rcases h5 with (h5 | h5 | h5 | h5 | h5)
      · -- Case where x % 5 = 0
        use x / 5, 0, 0
        omega
      · -- Case where x % 5 = 1
        use x / 5 - 3, 2, 0
        omega
      · -- Case where x % 5 = 2
        use (x - 12) / 5, 0, 1
        omega
      · -- Case where x % 5 = 3
        use (x - 8) / 5, 1, 0
        omega
      · -- Case where x % 5 = 4
        use (x - 24) / 5, 0, 2
        omega
    contradiction