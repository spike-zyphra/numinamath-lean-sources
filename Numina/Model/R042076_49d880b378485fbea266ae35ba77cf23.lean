import Mathlib

theorem number_theory_4880(n m : ℕ) (hcop : n.Coprime m) :
    (ArithmeticFunction.moebius n) * (ArithmeticFunction.moebius m) =
    ((ArithmeticFunction.moebius (n * m))) :=
  by
  rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime]
  . apply ArithmeticFunction.isMultiplicative_moebius
  all_goals try tauto