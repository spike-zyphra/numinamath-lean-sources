import Mathlib

theorem number_theory_52292 : IsGreatest {n : ℕ | ¬∃ x y, n = 8*x + 15*y} 97 := by
  constructor
  · -- Show 97 is indeed in the set, i.e., ¬∃ x y, (97 : ℕ) = 8 * x + 15 * y
    show ¬∃ x y, (97 : ℕ) = 8 * x + 15 * y
    rintro ⟨x, y, h⟩
    omega
  · -- Show that 97 is greatest, i.e., ∀ n, ¬∃ x y, n = 8*x + 15*y → n ≤ 97
    intro n hn
    by_contra h
    push_neg at h
    have h1 : ¬∃ x y, n = 8 * x + 15 * y := hn
    have h2 : n > 97 := h
    have h4 : ∃ x y, n = 8 * x + 15 * y := by
      have h5 : n > 97 := h2
      have h6 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
        omega
      rcases h6 with (h | h | h | h | h | h | h | h)
      · -- Case n % 8 = 0
        use n / 8, 0
        all_goals omega
      · -- Case n % 8 = 1
        use (n - 105) / 8, 7
        all_goals omega
      · -- Case n % 8 = 2
        use (n - 90) / 8, 6
        all_goals omega
      · -- Case n % 8 = 3
        use (n - 75) / 8, 5
        all_goals omega
      · -- Case n % 8 = 4
        use (n - 60) / 8, 4
        all_goals omega
      · -- Case n % 8 = 5
        use (n - 45) / 8, 3
        all_goals omega
      · -- Case n % 8 = 6
        use (n - 30) / 8, 2
        all_goals omega
      · -- Case n % 8 = 7
        use (n - 15) / 8, 1
        all_goals omega
    contradiction