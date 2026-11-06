import Mathlib

/- Show that if \( p \) is a prime number and \( a \) is an integer such that \( p \) does not divide \( a \) (denoted as \( p \nmid a \)), then \( a^{p-2} \) is the multiplicative inverse of \( a \) modulo \( p \).-/
theorem number_theory_4778 (p a : ℕ) (_ : 0 < a) (hp : Nat.Prime p) (hdiv : ¬p ∣ a) :
    a * a^(p - 2) ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hpge : 2 ≤ p := Nat.Prime.two_le hp
  -- we can rewrite a*a^(p-2) to a^(p-1)
  rw [← ZMod.eq_iff_modEq_nat, mul_comm, ← pow_succ]
  push_cast
  rw [show p - 2 + 1 = p - 1 by nth_rw 2 [← Nat.sub_add_cancel hpge]; simp]
  -- this is exactly fermat's little theorem
  apply ZMod.pow_card_sub_one_eq_one
  -- ensure that p doesn't divide a
  intro ha
  rw [show (0 : ZMod p) = ((0 : ℕ) : ZMod p) by simp, ZMod.eq_iff_modEq_nat,
    Nat.modEq_zero_iff_dvd] at ha
  contradiction
