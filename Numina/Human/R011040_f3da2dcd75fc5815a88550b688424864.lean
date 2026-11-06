import Mathlib

/-The mentor gave the student to divide one number by another. The student got a quotient of 74 and a remainder of 22. Then he performed a check: he multiplied the quotient by the divisor and added the remainder to the product, thus obtaining 30214. It turned out that there was an error.
The student, while multiplying (during the check), read a six in the tens place of the divisor as a zero. Determine the dividend and the divisor.-/

theorem algebra_227400 {x y: ℕ} (h1: x / y = 74) (h2: x % y = 22)
(h: x = 74 * 60 + 30214): x = 34654 ∧ y = 468 := by

  have o: x = 74 * y + 22 := by
    simp [← h1, ← h2]
    rw [Nat.div_eq_sub_mod_div]
    have o: y ∣ x - x % y := by
      apply Nat.dvd_sub_mod

    rw [Nat.dvd_iff_div_mul_eq] at o
    simp [o]
    omega

  simp at h
  simp [h] at o
  simp [h]
  omega
