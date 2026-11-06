import Mathlib

theorem number_theory_213683 :
    (∀ x y z : ℤ, 7 ∣ x^3 + y^3 + z^3 → 7 ∣ x ∨ 7 ∣ y ∨ 7 ∣ z) ∧
    (∃ x y z t : ℤ, 7 ∣ x^4 + y^4 + z^4 + t^4 ∧ ¬(7 ∣ x) ∧ ¬(7 ∣ y) ∧ ¬(7 ∣ z) ∧ ¬(7 ∣ t)) := by
  constructor
  · -- Assume that for all integers x, y, z, if 7 divides x^3 + y^3 + z^3, then at least one of them is divisible by 7
    intro x y z h
    by_contra h1
    push_neg at h1
    have h2 : ¬ (7 ∣ x) := h1.1
    have h3 : ¬ (7 ∣ y) := h1.2.1
    have h4 : ¬ (7 ∣ z) := h1.2.2
    have h5 : x % 7 = 1 ∨ x % 7 = 2 ∨ x % 7 = 3 ∨ x % 7 = 4 ∨ x % 7 = 5 ∨ x % 7 = 6 := by
      omega
    have h6 : y % 7 = 1 ∨ y % 7 = 2 ∨ y % 7 = 3 ∨ y % 7 = 4 ∨ y % 7 = 5 ∨ y % 7 = 6 := by
      omega
    have h7 : z % 7 = 1 ∨ z % 7 = 2 ∨ z % 7 = 3 ∨ z % 7 = 4 ∨ z % 7 = 5 ∨ z % 7 = 6 := by
      omega
    have hx3 : x^3 % 7 = 1 ∨ x^3 % 7 = 6 := by
      rcases h5 with (h | h | h | h | h | h) <;> norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    have hy3 : y^3 % 7 = 1 ∨ y^3 % 7 = 6 := by 
      rcases h6 with (h | h | h | h | h | h) <;> norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    have hz3 : z^3 % 7 = 1 ∨ z^3 % 7 = 6 := by 
      rcases h7 with (h | h | h | h | h | h) <;> norm_num [h, pow_succ, Int.add_emod, Int.mul_emod]
    omega
  · -- Show that there exist integers x, y, z, t such that 7 divides x^4 + y^4 + z^4 + t^4 but 7 does not divide any of them
    use 1, 2, 2, 2
    constructor
    · -- Show that 7 divides the sum
      norm_num
    · -- Show that 7 does not divide any of x, y, z, t
      constructor
      · -- Show that 7 does not divide 1
        norm_num
      constructor
      · -- Show that 7 does not divide 2
        norm_num
      constructor
      · -- Show that 7 does not divide 2
        norm_num
      · -- Show that 7 does not divide 2
        norm_num