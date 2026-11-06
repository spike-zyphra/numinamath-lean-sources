import Mathlib

def N (k : ℕ) := k.factorial + 1

/- Let $k$ be a positive integer. Let $N_k = k! + 1$. Show that there exists a prime number $p$ such that $p$ divides $N_k$ and $p > k$. -/
theorem number_theory_636110
  (k : ℕ) (kpos : k > 0)
  : ∃ p : ℕ, p.Prime ∧ p > k ∧ p ∣ N k :=
by
  -- use any prime factor
  have ⟨p, ph⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ N k := by
    have nonemp : (N k).primeFactorsList ≠ [] := by
      by_contra c
      have := (Nat.primeFactorsList_eq_nil _).mp c
      have : N k ≤ 1 := by omega
      simp [N] at this
      apply Nat.factorial_ne_zero
      assumption
    let p := (N k).primeFactorsList.head nonemp
    use p
    have : p ∈ (N k).primeFactorsList := by
        exact List.head_mem nonemp
    simp at this
    constructor
    . tauto
    . tauto
  use p
  constructor
  . tauto
  constructor; swap
  . tauto
  . -- proof by contra.
    by_contra c
    simp at c
    rcases ph with ⟨ph1,ph2⟩
    have : p ∣ k.factorial := by exact (Nat.Prime.dvd_factorial ph1).mpr c
    simp [N] at ph2
    have : p ∣ 1 := by
      exact (Nat.dvd_add_iff_right this).mpr ph2
    have : p ≤ 1 := by exact (Nat.Prime.dvd_factorial ph1).mp this
    interval_cases p
    <;> norm_num at ph1
