import Mathlib

theorem number_theory_228863 : IsGreatest {n | ¬∃ k l, n = 3 * k + 7 * l} 11 := by
  constructor
  · -- Show 11 is in the set
    show ¬∃ k l, 11 = 3 * k + 7 * l
    intro h
    rcases h with ⟨k, l, h⟩
    omega
  · -- Show any n in the set ≤ 11
    intro n hn
    have hn' : ¬∃ k l, n = 3 * k + 7 * l := hn
    by_contra h
    push_neg at h
    have h12 : ∃ k l, n = 3 * k + 7 * l := by
      have h1 : n > 11 := by omega
      have h2 : n ≥ 12 := by omega
      have h3 : ∃ k l, n = 3 * k + 7 * l := by
        have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases h4 with (h4 | h4 | h4)
        · -- Case where n % 3 = 0
          use n / 3, 0
          omega
        · -- Case where n % 3 = 1
          use (n - 7) / 3, 1
          omega
        · -- Case where n % 3 = 2
          use (n - 14) / 3, 2
          omega
      exact h3
    obtain ⟨k, l, hk⟩ := h12
    exfalso
    exact hn ⟨k, l, hk⟩