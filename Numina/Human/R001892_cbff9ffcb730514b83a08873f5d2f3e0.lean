import Mathlib

set_option maxRecDepth 10000
/- We are tasked to compute the number of positive divisors of 2121 which have a units digit of 1. -/
theorem number_theory_43033 :
    {x : ℕ | x > 0 ∧ x ∣ 2121 ∧ (x % 10) = 1}.encard = 4 := by
  -- Start by factoring 2121.
  have h1 : 2121 = 3 * 707 := rfl
  have h2 : 707 = 7 * 101 := rfl
  have h3 : Nat.Prime 101 := by norm_num -- Verify that 101 is a prime number.
  -- List the divisors of 2121: 1, 3, 7, 21, 101, 303, 707, and 2121.
  let divisors : Finset ℕ := {1, 3, 7, 21, 101, 303, 707, 2121}
  let res : List ℕ := List.range 2122 |>.filter (fun x => x ∣ 2121)
  have : res.toFinset = divisors := by decide
  have hdivisors : ∀ x, x ∣ 2121 ↔ x ∈ divisors := by
    intro x
    constructor
    · intro hx
      simp [← this, res, hx]
      by_contra h
      suffices ¬x ∣ 2121 by exact this hx
      apply Nat.not_dvd_of_pos_of_lt
      norm_num
      omega
    · intro hx
      simp [divisors] at hx
      rcases hx with (hx | hx | hx | hx | hx | hx | hx | hx)
      all_goals simp [hx]
      all_goals omega
  -- Filter divisors ending in 1: 1, 21, 101, 2121.
  let divisors_units_digit_1 : Finset ℕ := {1, 21, 101, 2121}
  have h_units_digit_1 : {x |x > 0 ∧ x ∣ 2121 ∧ (x % 10) = 1} = divisors_units_digit_1 := by
    simp [divisors_units_digit_1]
    ext x
    constructor
    · intro hx
      simp at hx
      have := (hdivisors x).1 hx.2.1
      simp [divisors] at this
      rcases this with (hx | hx | hx | hx | hx | hx | hx | hx)
      all_goals try omega
      all_goals simp [hx]
    · intro hx
      simp [divisors] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      all_goals simp
      all_goals omega
  -- There are 4 such divisors: 1, 21, 101, 2121.
  rw [h_units_digit_1]
  simp only [Set.encard_coe_eq_coe_finsetCard]
  simp [divisors_units_digit_1]