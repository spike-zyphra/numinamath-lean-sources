import Mathlib

/-Let p be a prime number greater than 9. An ordered pair of digits
(a,b), where a∈{0,1,…,9} and b∈{1,2,…,9}, is such that the six-digit number 4a5b32 (which is arithmetically  is a multiple of 6p.
Assuming such a pair (a,b) exists, show that a+b=10.-/

theorem number_theory_639164 (p a b: ℕ) (lp: p = 11) (la: 0 ≤ a) (ra: a ≤ 9) (lb: 1 ≤ b) (rb: b ≤ 9)
  (h: 6 * p ∣ 400000 + a * 10000 + 5000 + b * 100 + 32): a + b = 10 := by
    have d2: 6 ∣ 400000 + a * 10000 + 5000 + b * 100 + 32 := by
      suffices 6 ∣ 6 * p by
        apply dvd_trans this h
      simp
    have d1: p ∣ 400000 + a * 10000 + 5000 + b * 100 + 32 := by
      suffices p ∣ 6 * p by
        apply dvd_trans this h
      simp
    clear h
    replace d2: 3 ∣ 400000 + a * 10000 + 5000 + b * 100 + 32 := by
      suffices 3 ∣ 6 by
        apply dvd_trans this d2
      norm_num
    replace d2: 3 ∣ a + b + 2 := by
      rw [show a + b + 2 = 400000 + a * 10000 + 5000 + b * 100 + 32 - 3 * (3333 * a + 33 * b + 135010) by omega]
      apply Nat.dvd_sub
      .
        clear d1
        omega
      .
        exact d2
      .
        simp
    apply exists_eq_mul_right_of_dvd at d2
    obtain ⟨k, h⟩ := d2
    set t:= k - 1
    replace h: a + b = 3 * t + 1 := by omega
    clear_value t
    suffices t = 3 by
      simp [h, this]
    have lt: t < 6 := by
      clear d1
      omega
    rw [show 400000 + a * 10000 + 5000 + b * 100 + 32 = 405032 + 9900 * a + 100 * (3 * t + 1) by rw [← h]; omega] at d1
    clear h
    rw [show 405032 + 9900 * a + 100 * (3 * t + 1) = 12 * (33761 + 825 * a + 25 * t) by ring] at d1
    replace d1: 11 ∣ 33761 + 825 * a + 25 * t := by
      apply Nat.Coprime.dvd_of_dvd_mul_left at d1
      rw [lp] at d1
      exact d1
      rw [lp]
      norm_num
    replace d1: 11 ∣ 2 + 3 * t := by
      rw [show 2 + 3 * t = 33761 + 825 * a + 25 * t - 11 * (3069 + 75 * a + 2 * t) by omega]
      apply Nat.dvd_sub
      .
        omega
      .
        tauto
      .
        simp
    clear *- d1 lt
    omega