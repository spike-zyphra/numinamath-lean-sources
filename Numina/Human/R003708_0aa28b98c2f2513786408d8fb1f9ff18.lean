import Mathlib

/-A five-digit number x starts with 4 and ends with 7,
and a five-digit number y starts with 9 and ends with 3.
It is known that the numbers x and y have a common five-digit divisor. Prove that 2y−x is divisible by 11. -/

theorem number_theory_209507 {x y: ℕ} (lx: 40000 ≤ x) (rx: x < 50000) (dx: x % 10 = 7)
  (ly: 90000 ≤ y) (ry: y < 100000) (dy: y % 10 = 3) (h: ∃ z, z ∣ x ∧ z ∣ y ∧ 10000 ≤ z ∧ z < 100000):
    11 ∣ (2 * y - x) := by

    obtain ⟨z, ox, oy, lz, rz⟩ := h
    apply exists_eq_mul_right_of_dvd at ox
    obtain ⟨a, ox⟩ := ox
    apply exists_eq_mul_right_of_dvd at oy
    obtain ⟨b, oy⟩ := oy

    -- upper bound of a and b
    have la: a < 5 := by nlinarith
    replace la: a ≤ 4 := by omega
    have lb: b ≤ 9 := by nlinarith

    -- show that a and b are odd
    have ia: Odd a := by
      replace dx: x % 10 % 2 = 7 % 2 := by
        rw [dx]
      rw [Nat.mod_mod_of_dvd] at dx
      norm_num at dx
      have j: 2 ∣ x - 1 := by
        rw [← dx]
        apply Nat.dvd_sub_mod
      have jx: Odd x := by
        rw [odd_iff_exists_bit1]
        apply exists_eq_mul_right_of_dvd  at j
        obtain ⟨k, jx⟩ := j
        use k
        omega
      rw [ox] at jx
      apply Nat.Odd.of_mul_right at jx
      exact jx
      norm_num
    have ib: Odd b := by
      replace dy: y % 10 % 2 = 3 % 2 := by
        rw [dy]
      rw [Nat.mod_mod_of_dvd] at dy
      norm_num at dy
      have j: 2 ∣ y - 1 := by
        rw [← dy]
        apply Nat.dvd_sub_mod
      have jy: Odd y := by
        rw [odd_iff_exists_bit1]
        apply exists_eq_mul_right_of_dvd  at j
        obtain ⟨k, jy⟩ := j
        use k
        omega
      rw [oy] at jy
      apply Nat.Odd.of_mul_right at jy
      exact jy
      norm_num

    -- then we show that a = 3
    have ea: a = 3 := by
      interval_cases a
      .
        norm_num at ia
      .
        have lb: 3 ≤ b := by
          by_contra! s
          interval_cases b
          .
            simp [oy] at ly
          .
            nlinarith
          .
            absurd ib
            simp
        nlinarith
      .
        absurd ia
        simp
      .
        trivial
      .
        absurd ia
        simp
        decide

    set w:= z % 10 with hw
    simp [ea] at *

    -- then we show that w = 9
    have ew: w = 9 := by
      rw [ox] at dx
      rw [Nat.mul_mod] at dx
      have hw: z % 10 = w := by simp [w]
      rw [hw] at dx
      norm_num at dx
      have lw: w ≤ 9 := by omega
      clear_value w
      clear * - lw dx
      interval_cases w
      all_goals omega

    -- then we show that b = 7
    have eb: b = 7 := by
      rw [oy] at dy
      rw [Nat.mul_mod] at dy
      simp [w] at ew
      rw [ew] at dy
      norm_num at dy
      clear * - lb dy
      interval_cases b
      all_goals norm_num at dy
      simp

    -- finally, we obtain the result
    rw [eb] at oy
    simp [ox, oy]
    rw [show 2 * (z * 7) - z * 3 = 11 * z by omega]
    simp