import Mathlib

theorem number_theory_132637 (r : ℕ) (hr : 0 < r) :
    ∃ n, ∀ i ∈ Finset.range r, ¬Nat.Prime (n + i) := by
  use (r + 1).factorial + 2
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : i < r := by linarith
  have h3 : i + 2 ≤ (r + 1 : ℕ) := by
    omega
  have h5 : (i + 2) ∣ (r + 1).factorial := by
    apply Nat.dvd_factorial
    all_goals
      omega
  have h4 : (i + 2) ∣ ((r + 1).factorial + (i + 2)) := by
    apply Nat.dvd_add
    · exact h5
    · exact Nat.dvd_refl (i + 2)
  have h7 : ¬Nat.Prime ((r + 1).factorial + (i + 2)) := by
    apply Nat.not_prime_of_dvd_of_lt h4
    all_goals
      have h5 : (r + 1).factorial > 0 := by
        apply Nat.factorial_pos
      have h8 : (r + 1).factorial + (i + 2) > (i + 2) := by
        linarith
      all_goals
        omega
  have h8 : (r + 1).factorial + 2 + i = (r + 1).factorial + (i + 2) := by
    omega
  rw [show (r + 1).factorial + 2 + i = (r + 1).factorial + (i + 2) by omega]
  exact h7