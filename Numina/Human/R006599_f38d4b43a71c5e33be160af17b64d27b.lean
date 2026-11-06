import Mathlib
/- Let $p$ be a prime number. Determine the remainder when $(p-1)^{p-2}$ is divided by $p$. Show the answer is $p-1$. -/
theorem number_theory_638998 (p : ℕ) (hp : Nat.Prime p) : (p - 1) ^ (p - 2) % p = p - 1:= by
  -- First establish that p > 1 since p is prime
  have h1 : p > 1:= by exact Nat.Prime.one_lt hp
  -- We will prove this by showing modular equivalence
  refine Nat.mod_eq_of_modEq ?_ (by omega)
  -- Case split: handle p = 2 separately
  by_cases h2 : p = 2
  .
    -- For p = 2 case, direct computation shows the result
    subst p
    simp
    rfl
  .
    -- For p > 2 case, first show p-2 > 0
    replace h1 : p - 2 > 0:= by omega
    clear h2
    -- Show that (p-1)^(p-2) ≥ p-1 using properties of powers
    have h2 : (p - 1) ^ (p - 2) ≥ p - 1:= by
      refine Nat.le_self_pow (by omega) (p - 1)
    -- Prove divisibility to establish modular equivalence
    suffices p ∣ (p - 1) ^ (p - 2) - (p - 1) by exact Nat.ModEq.symm ((fun {n a b} h => (Nat.modEq_iff_dvd' h).mpr) h2 this)
    -- Convert to integer arithmetic
    zify
    field_simp
    -- Show that p-1+1 = p (helper for algebraic manipulation)
    have h3 : p - 1 + 1 = p:= by omega
    zify at h3
    -- Express p-1 in terms of p
    replace h3 : (↑(p - 1) : ℤ) = (↑p : ℤ) - 1:= by linarith
    rw [h3]
    clear h3
    -- Reduce to showing modular congruence
    suffices (p - 1) ^ (p - 2) ≡ p - 1 [ZMOD p] by exact Int.ModEq.dvd (id (Int.ModEq.symm this))
    -- Show that p-1 ≡ -1 (mod p)
    have h3 : p - 1 ≡ -1 [ZMOD p]:= by
      suffices (↑p : ℤ) ∣ p - 1 - (-1) by exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) this)
      simp
    -- Use this to show (p-1)^(p-2) ≡ -1 (mod p)
    suffices (p - 1) ^ (p - 2) ≡ -1 [ZMOD p] by exact Int.ModEq.trans this (id (Int.ModEq.symm h3))
    -- Show that powers preserve modular congruence
    replace h3 : (p - 1) ^ (p - 2) ≡ (-1) ^ (p - 2) [ZMOD p]:= by exact Int.ModEq.pow (p - 2) h3
    -- Show that p ≠ 2 for this case
    replace h1 : p ≠ 2:= by omega
    -- Prove that p is odd (since it's prime and not 2)
    have h4 : Odd p:= by exact Nat.Prime.odd_of_ne_two hp h1
    -- Show that p-2 is odd when p is odd and not 2
    have h5 : Odd (p - 2):= by
      by_contra H
      simp at H
      have h5 : Even 2:= by decide
      replace H : Even (p - 2 + 2):= by exact Even.add H h5
      replace h1 : p > 1:= by exact Nat.Prime.one_lt hp
      rw [show p - 2 + 2 = p by omega] at H
      absurd h4
      simp
      exact H
    -- Use the fact that (-1) raised to an odd power equals -1
    rw [show (-1) ^ (p - 2) = -1 by exact Odd.neg_one_pow h5] at h3
    exact h3
