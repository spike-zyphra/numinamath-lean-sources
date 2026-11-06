import Mathlib

theorem number_theory_4388 (n : ℕ) (h₀ : n ≠ 0) (h₁ : (Nat.primeFactors n).card = 3)
    (h₂ : ∑ d in n.divisors, d = 312) :
    n = 126 := by 
  -- First, let's provide a proof that $n \leq 312$.
  have h3 : n ≤ 312 := by
    have h5 : n ∈ n.divisors := by
      simp [Nat.mem_divisors, h₀]
    have h6 : ∑ d in n.divisors, d ≥ n := by
      apply Finset.single_le_sum (fun x hx => by
        simp
      ) h5
    linarith
  -- Need to prove $n = 126$
  interval_cases n <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] at h₁ h₂ ⊢
  <;> try { contradiction }
  <;> try { trivial }