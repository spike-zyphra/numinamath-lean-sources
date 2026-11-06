import Mathlib

theorem number_theory_276913 (n : ℕ) :
    133 ∣ (11^(n + 2) + 12^(2 * n + 1)) := by
  have h1 : ∀ (n : ℕ), 133 ∣ (11 ^ (n + 2) + 12 ^ (2 * n + 1)) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : (11 ^ ((k + 1) + 2) + 12 ^ (2 * (k + 1) + 1)) =
          11 * (11 ^ (k + 2)) + 144 * (12 ^ (2 * k + 1)) := by 
        ring_nf
      have h3 : 133 ∣ (11 * (11 ^ (k + 2)) + 144 * (12 ^ (2 * k + 1)) ) := by
        omega
      rw [h2]
      all_goals try omega
  specialize h1 n
  simpa using h1