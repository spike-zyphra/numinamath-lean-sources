import Mathlib

theorem number_theory_229691 (n : ℕ) : 9 ∣ (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) := by
  have h1 : ∀ n : ℕ, 9 ∣ (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) := by
    intro n
    have h2 : ∀ n : ℕ, 9 ∣ (n ^ 3 + (n + 1) ^ 3 + (n + 2) ^ 3) := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ k ih =>
        have h5 : (k + 1 : ℕ) ^ 3 + (k + 1 + 1 : ℕ) ^ 3 + (k + 1 + 2 : ℕ) ^ 3 =
          (k ^ 3 + (k + 1) ^ 3 + (k + 2) ^ 3) + 9 * (k ^ 2 + 3 * k + 3) := by
          ring_nf
        rw [h5]
        omega
    specialize h2 n
    simpa using h2
  specialize h1 n
  simpa using h1