import Mathlib

/-The sum of the digits of a four-digit number is 27.
Prove that the sum of that number
and the number written with the same digits but in reverse order is divisible by 27.-/

theorem number_theory_243206 {n: ℕ} (a b c d: ℕ)
(hn: n = 1000 * a + 100 * b + 10 * c + d) (h: a + b + c + d = 27):
  27 ∣ (n + (1000 * d + 100 * c + 10 * b + a)) := by

    rw [hn]
    rw [show 1000 * a + 100 * b + 10 * c + d + (1000 * d + 100 * c + 10 * b + a)
    = 1001 * (a + d) + 110 * (b + c) by ring]
    rw [show 1001 * (a + d) + 110 * (b + c) = 891 * (a + d) + 110 * (a + b + c + d) by ring]
    simp [h]
    have o: 27 ∣ 891 := by norm_num
    have v: 891 ∣ 891 * (a + d) := by simp
    apply dvd_trans o v
    