import Mathlib

/- Show that if \( n \) is a positive integer and \( a \) and \( b \) are integers that are relatively prime to \( n \), such that the orders of \( a \) and \( b \) modulo \( n \) are coprime (i.e., \( \text{gcd}(\operatorname{ord}_{n} a, \operatorname{ord}_{n} b) = 1 \)), then the order of the product \( ab \) modulo \( n \) is equal to the product of the orders of \( a \) and \( b \) modulo \( n \) (i.e., \( \operatorname{ord}_{n}(ab) = \operatorname{ord}_{n} a \cdot \operatorname{ord}_{n} b \)).-/
theorem number_theory_4996 (n a b: ℕ) (hna : Nat.Coprime a n) (hnb : Nat.Coprime b n)
    (hgcd : Nat.gcd (orderOf (ZMod.unitOfCoprime a hna)) (orderOf (ZMod.unitOfCoprime b hnb)) = 1) :
    orderOf (ZMod.unitOfCoprime (a * b) (Nat.coprime_mul_iff_left.mpr ⟨hna, hnb⟩)) =
    (orderOf (ZMod.unitOfCoprime a hna)) * (orderOf (ZMod.unitOfCoprime b hnb)) := by
  --this is exactly the proposition Commute.orderOf_mul_eq_mul_orderOf_of_coprime in Mathlib
  have r1 : Commute (ZMod.unitOfCoprime a hna) (ZMod.unitOfCoprime b hnb) := by
    rw [commute_iff_eq, mul_comm]
  have r2 : ZMod.unitOfCoprime (a * b) (Nat.coprime_mul_iff_left.mpr ⟨hna, hnb⟩) =
      (ZMod.unitOfCoprime a hna) * (ZMod.unitOfCoprime b hnb) := by
    rw [← Units.eq_iff]; simp
  rw [r2]; exact Commute.orderOf_mul_eq_mul_orderOf_of_coprime r1 hgcd
