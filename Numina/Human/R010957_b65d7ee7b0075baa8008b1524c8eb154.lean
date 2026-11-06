import Mathlib

/- We define the set of divisors of 100 and the set of integers between 1 and 100. -/
def D := Nat.divisors 100
def Z := Finset.Icc 1 100

/- Let $D$ be the set of divisors of 100 . Let $Z$ be the set of integers between 1 and 100, inclusive. Mark chooses an element $d$ of $D$ and an element $z$ of $Z$ uniformly at random. What is the probability that $d$ divides $z$ ? -/
theorem number_theory_609244 :
    ((D ×ˢ Z).filter (fun (d, z) => d ∣ z)).card / (D.card * Z.card) = (217 / 900 : ℚ) := by
  -- We can compute the size of the set of pairs (d, z) such that d divides z
  native_decide
