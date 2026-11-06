import Mathlib

open Nat

/-- The prime factors of `M!` are exactly the primes `p` with `p ≤ M`. -/
theorem primeFactors_factorial
  {M : ℕ}
  (h : 1 < M) :
  Nat.totient (M !) = M ! * ∏ p ∈ (Finset.range (M + 1)).filter (fun p => Nat.Prime p), (1 - 1 / (p: ℚ)) := by

  -- use the Euler's product formula for the totient function
  have h1: ↑(φ M !) = ↑M ! * ∏ p ∈ (M !).primeFactors, (1 - (p: ℚ)⁻¹) := Nat.totient_eq_mul_prod_factors (M !)

  rw [h1]

  -- prove the equality of sets
  -- (M !).primeFactors = {p | Prime p ∧ p ≤ M}
  have primeFactors_fact: ∀(M : ℕ),
    (M !).primeFactors = (Finset.range (M + 1)).filter (fun p => Nat.Prime p) := by
    -- extensionality on finsets
    intro M
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · -- p ∈ (M !).primeFactors → p ≤ M
      intro h
      simp at h
      have :p ≤ M := (Nat.Prime.dvd_factorial h.1).mp h.2.1
      exact ⟨by omega, h.1⟩
    · -- p ≤ M → p ∈ (M !).primeFactors
      intro h
      simp
      have h2 : p ∣ M ! := by
        exact (Nat.Prime.dvd_factorial h.2).mpr (by omega: p ≤ M)
      exact ⟨h.2, h2, by positivity⟩

  -- reduce to prove the equality of sets
  congr
  . exact primeFactors_fact M
  . simp
