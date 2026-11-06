import Mathlib

/- 330. Simple pairs. Let $n$ be a natural number greater than 3. Prove that there exist two odd prime numbers $p_{1}$ and $p_{2}$, such that $2 n - p_{1}$ is divisible by $p_{2}$ (the case $2 n - p_{1} < 0$ is not excluded). -/
theorem number_theory_271484 (n : ℕ) (hn : n > 3) :
    ∃ p1 p2 : ℕ, Odd p1 ∧ Odd p2 ∧ Prime p1 ∧ Prime p2 ∧
      (2 * n - p1 : ℤ) % p2 = 0 := by
  -- first pick a prime that doesn't divide 2 * n by picking a prime ≥ 2 * n + 1
  obtain ⟨p2, h1, h2⟩ := Nat.exists_infinite_primes (2 * n + 1)
  -- this prime is not equal to 2, so odd
  have h3 : p2 ≠ 2 := by linarith
  replace h3 : Odd p2 := by exact h2.odd_of_ne_two h3
  -- p2 is not 0, needed later
  haveI : NeZero p2 := by
    constructor
    exact h2.ne_zero
  -- now 2*n, is a unit in residues modulo p2 as p2 does not divide 2*n
  have h4 : IsUnit (2 * n : ZMod p2) := by
    norm_cast
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm]
    apply Nat.Prime.coprime_iff_not_dvd h2 |>.mpr
    apply mt <| Nat.le_of_dvd (by linarith)
    omega
  -- now take a prime p1 that is ≡ 2*n (mod p2) by drichlet theorem, in fact take one larger than 2
  obtain ⟨p1, h5, h6, h7⟩ := Nat.forall_exists_prime_gt_and_eq_mod h4 2
  -- this prime is odd
  have h8 : Odd p1 := by exact h6.odd_of_ne_two (by linarith)
  have h9 : Prime p1 := by exact Nat.prime_iff.mp h6
  have h10 : Prime p2 := by exact Nat.prime_iff.mp h2
  -- now we use p1, p2 as witness
  use p1, p2
  simp [h3, h8, h9, h10]
  -- the p1 ≡ 2*n (mod p2) is equivalent to our target
  replace h7 : (↑ (p1 : ℤ) : ZMod p2) = ↑ (2 * n : ℤ) := by
    norm_cast at h7 ⊢
  rwa [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd] at h7