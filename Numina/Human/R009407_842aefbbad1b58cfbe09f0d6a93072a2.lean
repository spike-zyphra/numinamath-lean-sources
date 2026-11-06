import Mathlib

/- Theorem 8.4 states that if the order of \( a \) modulo \( m \) is \( t \) (denoted as \( \operatorname{ord}_{m} a = t \)), and if \( u \) is a positive integer, then the order of \( a^u \) modulo \( m \) is given by the formula \( \operatorname{ord}_{m}(a^{u}) = \frac{t}{(t, u)} \), where \( (t, u) \) denotes the greatest common divisor of \( t \) and \( u \).-/
theorem number_theory_4988 (a n u: ℕ)(_ : NeZero n) (_ : 0 < u)(han : Nat.Coprime a n) :
    orderOf ((ZMod.unitOfCoprime a han) ^ u) =
    orderOf (ZMod.unitOfCoprime a han) / Nat.gcd (orderOf (ZMod.unitOfCoprime a han)) u :=
  --The problem is exactly the proposition orderOf_pow in Mathlib.
  orderOf_pow (ZMod.unitOfCoprime a han)
