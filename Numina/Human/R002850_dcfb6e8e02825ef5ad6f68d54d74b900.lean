import Mathlib

/- (Wilson's Theorem) Let $N>1$ be a natural number, show that $(N-1)!\equiv-1\pmod{N}$ if and only if $N$ is prime. -/
theorem number_theory_121989 {N : ℕ} (hN : N > 1) :
    Nat.factorial (N - 1) + 1 ≡ 0 [MOD N] ↔ Nat.Prime N := by
  -- we will use wilson's theorem which states N is prime iff N! = -1 (mod N)
  have h : Nat.Prime N ↔ ((N-1).factorial : ZMod N) = -1 := Nat.prime_iff_fac_equiv_neg_one (show N ≠ 1 by linarith)
  -- convert the ModEq to ZMod equation, then the result is obvious as ZMod N is a additive group
  rw [h, ← ZMod.eq_iff_modEq_nat]
  push_cast
  exact Iff.symm eq_neg_iff_add_eq_zero