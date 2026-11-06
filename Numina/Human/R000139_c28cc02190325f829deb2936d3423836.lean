import Mathlib

/- Show that if \( p \) is a prime number and \( a \) is an integer, then \( p \) divides \( a^{p} + (p-1)!a \).-/
theorem number_theory_4799 (p a : ℕ) (hp : p.Prime) :
    p ∣ a^p + Nat.factorial (p - 1) * a := by
  -- `ZMod.pow_card` and `ZMod.wilsons_lemma` need this fact
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.modEq_zero_iff_dvd, ← ZMod.eq_iff_modEq_nat]
  push_cast
  -- combining Fermat's little theorem and Wilson's theorem gives the desired result
  rw [ZMod.pow_card, ZMod.wilsons_lemma]
  ring
