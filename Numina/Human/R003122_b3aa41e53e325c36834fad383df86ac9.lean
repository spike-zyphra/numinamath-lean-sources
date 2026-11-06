import Mathlib

/- 21. [11] Call a number overweight if it has at least three positive integer divisors (including 1 and the number), and call a number obese if it has at least four positive integer divisors (including 1 and the number). How many positive integers between 1 and 200 are overweight, but not obese? -/
theorem number_theory_154758 :
    {n ∈ Finset.range 200 | n.divisors.card ≥ 3 ∧ n.divisors.card < 4}.card = 6 := by native_decide
