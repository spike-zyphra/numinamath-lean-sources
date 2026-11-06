import Mathlib

/- Corollary 8.1 states that if \( a \) and \( n \) are relatively prime integers with \( n > 0 \), then the order of \( a \) modulo \( n \), denoted as \( \operatorname{ord}_{n} a \), divides \( \phi(n) \), where \( \phi \) is Euler's totient function.-/
theorem number_theory_4984 (a n : ℕ)(nzn : NeZero n) (han : Nat.Coprime a n) :
    orderOf (ZMod.unitOfCoprime a han) ∣ n.totient := by
  --The problem is exactly the proposition orderOf_dvd_card in Mathlib.
  have : Fintype.card (ZMod n)ˣ = n.totient := ZMod.card_units_eq_totient n
  rw [← this]; exact orderOf_dvd_card
