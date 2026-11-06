import Mathlib

/- Show that if \( m \) is a positive integer and \( a \) is an integer relatively prime to \( m \) such that the order of \( a \) modulo \( m \) is \( m-1 \), then \( m \) is prime.-/
theorem number_theory_5001 (m a : ℕ)(ham : Nat.Coprime a m) [hm : NeZero m] [Fintype (ZMod m)ˣ]
    (mgt1 : 1 < m) (hord : orderOf (ZMod.unitOfCoprime a ham) = m - 1) :
    Nat.Prime m := by
  --we prove that if m is a positive integer and a is an integer relatively prime to m such taht the order of a modulo m is m-1, then m is prime
  --prepare to use the proposition Nat.totient_eq_iff_prime
  have r0 : 0 < m := by linarith
  have r1 := ZMod.card_units_eq_totient m
  have r2 := @orderOf_dvd_card (ZMod m)ˣ _ _ (ZMod.unitOfCoprime a ham)
  --show that m-1 is less or equal to m.totient
  rw [hord, r1] at r2; apply Nat.le_of_dvd at r2
  --show that m-1 is greater or equal to m.totient
  have r3 := Nat.totient_lt m mgt1
  apply Nat.le_sub_one_of_lt at r3
  --apply Nat.totient_eq_iff_prime
  have r4 : m - 1 = m.totient := by linarith
  rw [← Nat.totient_eq_iff_prime r0]; symm; exact r4
  exact Nat.totient_pos.mpr r0
