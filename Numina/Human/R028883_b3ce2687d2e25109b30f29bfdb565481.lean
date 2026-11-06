import Mathlib

/- Show that the following integers are Carmichael numbers:
a) \(2821 = 7 \cdot 13 \cdot 31\)
b) \(10585 = 5 \cdot 29 \cdot 73\)
c) \(29341 = 13 \cdot 37 \cdot 61\)
d) \(314821 = 13 \cdot 61 \cdot 397\)
e) \(27845 = 5 \cdot 17 \cdot 29 \cdot 113\)
f) \(172081 = 7 \cdot 13 \cdot 31 \cdot 61\)
g) \(564651361 = 43 \cdot 3361 \cdot 3907\).-/
theorem number_theory_4834 {x : ℕ} :
    (x=2821 → x.primeFactorsList = [7,13,31] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=10585 → x.primeFactorsList = [5,29,73] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=29341 → x.primeFactorsList = [13,37,61] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=314821 → x.primeFactorsList = [13,61,397] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=172081 → x.primeFactorsList = [7,13,31,61] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) ∧
    (x=564651361 → x.primeFactorsList = [43,3361,3907] → ∀ p ∈ x.primeFactorsList, p-1 ∣ x-1) := by
  -- verify by computation
  split_ands
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  . intro hx hxp
    rw [hxp, hx]
    intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
