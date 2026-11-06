import Mathlib

theorem number_theory_136150 {a b n ωa ωb : ℕ} (ha : Nat.Coprime a n) (hb : Nat.Coprime b n)
    (hωa : ωa = orderOf (a : ZMod n)) (hωb : ωb = orderOf (b : ZMod n)) (hcoprime : Nat.Coprime ωa ωb) :
    orderOf ((a * b) : ZMod n) = ωa * ωb := by 
  subst ωa ωb
  have h1 : Commute ((a : ZMod n)) ((b : ZMod n)) := by 
    rw [commute_iff_eq, mul_comm]
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime h1 hcoprime]