import Mathlib

/- Alex, Bob, Camille, and Danielle's mothers are comparing their children's ages. They observe that the sum of Alex, Bob, and Danielle's ages is fourteen times Camille's age. They also note that the sum of Alex and Bob's ages is six times Camille's age, and Bob's age is two years less than the difference in ages of Danielle and Alex. How old is Camille? -/
theorem algebra_19572 (a b c d : ℤ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h₀ : a + b + d = 14 * c) (h₁ : a + b = 6 * c)
    (h₂ : b = d - a - 2) : c = 1 := by omega
