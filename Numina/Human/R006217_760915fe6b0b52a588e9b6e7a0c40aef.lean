import Mathlib

/- Theorem: Suppose that $a$ and $b$ are positive integers satisfying the equation $a^b - b^a = 2$. Then $a$ and $b$ are congruent modulo 2. -/
theorem number_theory_634762 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : (a ^ b - b ^ a : ℤ) = 2) : a ≡ b [MOD 2] := by
  -- a ≡ b [MOD 2] ↔ a and b have the same parity.
  -- We write it as Even (b : ℤ) ↔ Even (a : ℤ) using some lemmas.
  simp only [← Int.natCast_modEq_iff, Nat.cast_ofNat, Int.modEq_iff_dvd, ← even_iff_two_dvd, Int.even_sub]
  -- We use `calc` block for chain of equivalences.
  calc Even (b : ℤ)
    -- b and b ^ a have the same parity since a is positive.
    _ ↔ Even (b ^ a : ℤ) := (Int.even_pow' ha.ne').symm
    -- a ^ b - b ^ a = 2, so b ^ a and a ^ b have the same parity.
    _ ↔ Even (a ^ b : ℤ) := (Int.even_sub.mp (h ▸ Int.even_iff.mpr rfl)).symm
    -- a ^ b and a have the same parity since b is positive.
    _ ↔ Even (a : ℤ) := Int.even_pow' hb.ne'