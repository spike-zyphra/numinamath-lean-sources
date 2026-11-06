import Mathlib

theorem number_theory_128453 : IsGreatest {n | ¬∃ x y, n = 8 * x + 11 * y} 69 := by
  constructor
  · -- Prove that 69 is in the set
    norm_num
    <;> omega
  · -- Prove that if n is in the set, then n ≤ 69
    intro n hn
    by_contra h1
    push_neg at h1
    have h2 : ∃ x y, n = 8 * x + 11 * y := by
      have h3 : n > 69 := h1
      have h4 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4)
      · -- Case n % 8 = 0
        use n / 8, 0
        omega
      · -- Case n % 8 = 1
        use (n - 33) / 8, 3
        omega
      · -- Case n % 8 = 2
        use (n - 66) / 8, 6
        omega
      · -- Case n % 8 = 3
        use (n - 11) / 8, 1
        omega
      · -- Case n % 8 = 4
        use (n - 44) / 8, 4
        omega
      · -- Case n % 8 = 5
        use (n - 77) / 8, 7
        omega
      · -- Case n % 8 = 6
        use (n - 22) / 8, 2
        omega
      · -- Case n % 8 = 7
        use (n - 55) / 8, 5
        omega
    have h3 : ∃ x y, n = 8 * x + 11 * y := h2
    contradiction