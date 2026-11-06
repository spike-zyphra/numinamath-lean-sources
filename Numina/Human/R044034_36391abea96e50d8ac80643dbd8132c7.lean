import Mathlib

/- Find all natural integers $a$ such that $a^{2}+a+1$ divides $a^{7}+3 a^{6}+3 a^{5}+3 a^{4}+a^{3}+a^{2}+3$ -/
theorem number_theory_103988 (a : ℕ) :
    (a^2 + a + 1) ∣ (a^7 + 3 * a^6 + 3 * a^5 + 3 * a^4 + a^3 + a^2 + 3) ↔
    a = 0 ∨ a = 1 := by

  -- Note that a^7 + 3 * a^6 + 3 * a^5 + 3 * a^4 + a^3 + a^2 + 3 = (a^2 + a + 1) * (a^5 + 2 * a^4 + a^2) + 3,
  -- where the first term is obviously divisible by a^2 + a + 1.
  rw [show a^7 + 3 * a^6 + 3 * a^5 + 3 * a^4 + a^3 + a^2 + 3 = (a^2 + a + 1) * (a^5 + 2 * a^4 + a^2) + 3 by ring]
  rw [← Nat.dvd_add_iff_right (Nat.dvd_mul_right _ _)]
  -- Now we proceed by cases.
  match a with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
    simp
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    nlinarith