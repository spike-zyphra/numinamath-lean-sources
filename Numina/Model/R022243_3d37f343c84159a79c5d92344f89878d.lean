import Mathlib

theorem number_theory_102350 :
    (1038^2) % 1000 = 444 ∧
    {n : ℕ | ∃ k, n = k^2 ∧ (n % 1000) = 444}.Infinite ∧
    ¬∃ n : ℕ, ∃ m, n = m^2 ∧ (n % 10000) = 4444 := by
  constructor
  · norm_num
  constructor
  · -- To prove the set is infinite, construct an injective map from the infinite set
    apply Set.infinite_of_injective_forall_mem (f := λ (a : ℕ) => (1038 + 1000 * a) ^ 2)
    · -- Show $f$ is injective.
      intro x y hxy
      simp at hxy ⊢
      all_goals
        nlinarith
    · -- Show that all elements of $f$ is in the set.
      intro a
      simp
      all_goals
        ring_nf
        <;> omega
  · -- Assume there exists such a square, derive a contradiction.
    rintro ⟨n, ⟨m, h1, h2⟩⟩
    have h3 : m ^ 2 % 16 = 0 ∨ m ^ 2 % 16 = 1 ∨ m ^ 2 % 16 = 4 ∨ m ^ 2 % 16 = 9 := by
      have h4 : m % 16 = 0 ∨ m % 16 = 1 ∨ m % 16 = 2 ∨ m % 16 = 3 ∨ m % 16 = 4 ∨ m % 16 = 5 ∨ m % 16 = 6 ∨ m % 16 = 7 ∨ m % 16 = 8 ∨ m % 16 = 9 ∨ m % 16 = 10 ∨ m % 16 = 11 ∨ m % 16 = 12 ∨ m % 16 = 13 ∨ m % 16 = 14 ∨ m % 16 = 15 := by 
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4) <;> simp [pow_two, Nat.mul_mod, h4] at *
    have h4 : n % 16 = 12 := by
      omega
    have h5 : m ^ 2 % 16 = 12 := by
      omega
    omega