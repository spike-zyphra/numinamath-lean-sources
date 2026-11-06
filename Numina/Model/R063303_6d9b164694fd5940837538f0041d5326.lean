import Mathlib

def isAttainable (n : ℕ) (m : ℕ) := ∃ s : ℕ → ℕ,
    s 0 = 1 ∧
    (∀ i, s (i + 1) = s i + 2 ∨ s (i + 1) = s i + n) ∧
    (∀ i, s (i + 2) = s (i + 1) * 2 ∨ s (i + 2) = s (i + 1) * n)

theorem number_theory_25197 (n : ℕ) :
    (n = 5 ∨ n = 7) → ∀ N, ∃ m > N, ¬isAttainable n m := by
  intro hn
  rcases hn with (rfl | rfl)
  · -- Case n = 5
    intro N
    use (4 * N + 5)
    constructor
    · -- Show that 4N + 5 > N
      linarith
    · -- Show that 4N + 5 is not attainable
      intro h
      rcases h with ⟨s, hs0, hadd, hmul⟩
      have h1 := hadd 0
      have h2 := hmul 0
      have h3 := hadd 1
      have h4 := hmul 1
      have h5 := hadd 2
      have h6 := hmul 2
      have h7 := hadd 3
      have h8 := hmul 3
      norm_num [hs0] at h1 h2 h3 h4 h5 h6 h7 h8
      all_goals
        omega
  · -- Case n = 7
    intro N
    use (3 * N + 4)
    constructor
    · -- Show that 3N + 4 > N
      linarith
    · -- Show that 3N + 4 is not attainable
      intro h
      rcases h with ⟨s, hs0, hadd, hmul⟩
      have h1 := hadd 0
      have h2 := hmul 0
      have h3 := hadd 1
      have h4 := hmul 1
      have h5 := hadd 2
      have h6 := hmul 2
      have h7 := hadd 3
      have h8 := hmul 3
      norm_num [hs0] at h1 h2 h3 h4 h5 h6 h7 h8
      all_goals
        omega