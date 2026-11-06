import Mathlib

theorem number_theory_143647 : IsGreatest {n | ¬∃ x y, n = x * 8 + y * 15} 97 := by
  constructor
  · -- Show 97 is in the set
    show ¬∃ x y, 97 = x * 8 + y * 15
    intro h
    rcases h with ⟨x, y, h_eq⟩
    omega
  · -- Show it's the greatest
    intro n hn
    have hn' : ¬∃ x y, n = x * 8 + y * 15 := hn
    by_contra h
    push_neg at h
    have h1 : ∃ x y, n = x * 8 + y * 15 := by
      have h2 : n ≥ 98 := by omega
      have h3 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by omega
      rcases h3 with (h | h | h | h | h | h | h | h)
      · -- Case n % 8 = 0
        use (n / 8), 0
        omega
      · -- Case n % 8 = 1
        use (n - 15 * 7) / 8, 7
        omega
      · -- Case n % 8 = 2
        use (n - 15 * 6) / 8, 6
        omega
      · -- Case n % 8 = 3
        use (n - 15 * 5) / 8, 5
        omega
      · -- Case n % 8 = 4
        use (n - 15 * 4) / 8, 4
        omega
      · -- Case n % 8 = 5
        use (n - 15 * 3) / 8, 3
        omega
      · -- Case n % 8 = 6
        use (n - 15 * 2) / 8, 2
        omega
      · -- Case n % 8 = 7
        use (n - 15 * 1) / 8, 1
        omega
    contradiction