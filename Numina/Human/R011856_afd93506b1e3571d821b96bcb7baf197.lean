import Mathlib

/-Given that the sum of 5 different positive odd numbers is 85.
Then the range of the largest number M among these five numbers is 21 ≤ M ≤ 69-/

theorem number_theory_305984 (x1 x2 x3 x4 x5: ℕ) (h1: 0 < x1) (h2: x1 < x2) (h3: x2 < x3) (h4: x3 < x4) (h5: x4 < x5)
(o1: Odd x1) (o2: Odd x2) (o3: Odd x3) (o4: Odd x4) (o5: Odd x5)
  (h: x1 + x2 + x3 + x4 + x5 = 85):
  21 ≤ x5 ∧ x5 ≤ 69 := by

    replace h1: 1 ≤ x1 := by omega
    replace h2: x1 + 2 ≤ x2 := by
      by_contra!
      replace o: x2 = x1 + 1 := by omega
      absurd o2
      simp
      rw [o,Nat.even_add_one]
      simp
      exact o1
    replace h3: x2 + 2 ≤ x3 := by
      by_contra!
      replace o: x3 = x2 + 1 := by omega
      absurd o3
      simp
      rw [o,Nat.even_add_one]
      simp
      exact o2
    replace h4: x3 + 2 ≤ x4 := by
      by_contra!
      replace o: x4 = x3 + 1 := by omega
      absurd o4
      simp
      rw [o,Nat.even_add_one]
      simp
      exact o3
    replace h5: x4 + 2 ≤ x5 := by
      by_contra!
      replace o: x5 = x4 + 1 := by omega
      absurd o5
      simp
      rw [o,Nat.even_add_one]
      simp
      exact o4
    constructor
    .
      nlinarith
    .
      nlinarith