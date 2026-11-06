import Mathlib

theorem number_theory_602356 : IsGreatest {n | ¬∃ k l, n = 3*k + 7*l} 11 := by
  constructor
  · -- Show 11 ∈ {n | ¬∃ k l, n = 3 * k + 7 * l}
    show ¬∃ k l, 11 = 3 * k + 7 * l
    rintro ⟨k, l, h⟩
    omega
  · -- Show there is no greater n in the set
    intro n hn
    have h : ¬∃ k l, n = 3 * k + 7 * l := by
      simpa using hn
    by_contra h1
    push_neg at h1
    have h2 : ∃ k l, n = 3 * k + 7 * l := by
      have h3 : n > 11 := h1
      have h4 : n ≥ 12 := by omega
      have h5 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h5 with (h5 | h5 | h5)
      · -- Case where n % 3 = 0
        use n / 3, 0
        omega
      · -- Case where n % 3 = 1
        use (n - 7) / 3, 1
        omega
      · -- Case where n % 3 = 2
        use (n - 14) / 3, 2
        omega
    contradiction