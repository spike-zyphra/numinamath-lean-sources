import Mathlib

theorem number_theory_4825 {A : Set ℕ} (hA : A = {x | ∃ p : ℕ, x = 4 * p + 1}) : 
    (∃ B ⊆ A, {x : ℕ | ∃ n : ℕ , x = n ^ 2 ∧ x ∈ B }.Infinite) ∧ ∀ x ∈ A, Nat.Prime x → x ^ 2 ≡ 1 [MOD 24] := by
  constructor
  · -- Show there exists a subset B ⊆ A with infinitely many squares
    use {x : ℕ | ∃ k : ℕ, x = (2 * k + 1) ^ 2}
    constructor
    · -- Show that {x | ∃ k, x = (2k + 1)²} ⊆ A
      intro x hx
      rcases hx with ⟨k, rfl⟩
      rw [hA]
      use k ^ 2 + k
      all_goals ring
    · -- Show that {x ∈ ℕ | ∃ n ∈ ℕ, x = n ^ 2 ∧ x ∈ B} is infinite
      apply Set.infinite_of_injective_forall_mem (f := λ (k : ℕ) => (2 * k + 1) ^ 2)
      · -- Show that f is injective
        intro k l h
        simp at h
        nlinarith
      · -- Show that all elements of f are in the set
        intro k
        simp
  · -- Show that if x ∈ A and x is prime, then x^2 ≡ 1 [MOD 24]
    intro x hx h_prime
    rw [hA] at hx
    rcases hx with ⟨p, hx_eq⟩
    have h1 : x % 4 = 1 := by
      omega
    by_cases h2 : x > 3
    · -- Assume x > 3
      have h3 : x % 3 = 1 ∨ x % 3 = 2 := by
        by_contra h
        push_neg at h
        have : x % 3 = 0 := by omega
        have h4 : x ≠ 3 := by linarith
        have h5 : ¬Nat.Prime x := by
          apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ x by omega)
          all_goals linarith
        contradiction
      have h8 : x % 8 = 1 ∨ x % 8 = 5 := by
        omega
      have h9 : x ^ 2 % 3 = 1 := by
        rcases h3 with (h3 | h3)
        · -- x % 3 = 1
          simp [Nat.pow_mod, h3]
        · -- x % 3 = 2
          simp [Nat.pow_mod, h3]
      have h10 : x ^ 2 % 8 = 1 := by
        rcases h8 with (h8 | h8)
        · -- x % 8 = 1
          simp [Nat.pow_mod, h8]
        · -- x % 8 = 5
          simp [Nat.pow_mod, h8]
      simp [Nat.ModEq] at *
      omega
    · -- Assume x ≤ 3
      interval_cases x <;> norm_num [Nat.ModEq] at *
      all_goals tauto