import Mathlib

lemma lemma_1 (n : ℕ) : 11 ∣ 12^n - 1 := by
  have h1 : ∀ (n : ℕ), 11 ∣ 12 ^ n - 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : 12 ^ (n + 1) - 1 = 12 * (12 ^ n) - 1 := by
        ring_nf
      rw [h2]
      omega
  apply h1 n


theorem number_theory_241337 (n : ℕ) :
    11 ∣ 12^n - 22 * n - 1 := by
  have h1 : 11 ∣ 12 ^ n - 1 := lemma_1 n
  have h2 : 11 ∣ 22 * n := by
    use 2 * n
    all_goals
      ring_nf
  have h3 : 11 ∣ (12 ^ n - 1 - 22 * n : ℕ) := by
    exact Nat.dvd_sub' h1 h2
  have h4 : (12 ^ n - 22 * n - 1 : ℕ) = (12 ^ n - 1 - 22 * n : ℕ) := by
    cases n with
    | zero =>
      all_goals
        omega
    | succ n =>
      all_goals
        omega
  rw [h4]
  exact h3