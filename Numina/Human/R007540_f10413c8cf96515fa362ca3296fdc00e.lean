import Mathlib

set_option maxRecDepth 100000
/-Compute the largest positive integer such that
2007! / 2007 ^ n is an integer.-/

theorem number_theory_608191: IsGreatest {n: ℕ | 2007 ^ n ∣ Nat.factorial 2007} 9 := by
  have fact: ¬ 223 ^ 10 ∣ Nat.factorial 2007 := by
    simp [Nat.factorial]
    norm_num
  constructor

  -- the goal is to show that 2007 ^ 9 ∣ Nat.factorial 2007 --
  . simp [Nat.factorial]
    norm_num

  -- the goal is to show the upper bound --
  . intro n
    simp
    intro h
    replace h: 223 ^ n ∣ Nat.factorial 2007 := by
      have eq: 2007 ^ n = 223 ^ n * 9 ^ n := by
        rw [show 2007 = 223 * 9 by norm_num]
        apply Nat.mul_pow
      have o: 223 ^ n ∣ 2007 ^ n := by
        rw [eq]
        apply Nat.dvd_mul_right
      apply Nat.dvd_trans o h
    by_contra! no
    let m:= n - 10
    have hm: n = m + 10 := by simp only [m]; symm; apply Nat.sub_add_cancel; linarith only [no]
    rw [hm] at h
    clear hm no
    clear_value m
    have o: 223 ^ 10 ∣ 223 ^ (m + 10) := by
      rw [show 223 ^ (m + 10) = 223 ^ 10 * 223 ^ m by ring]
      apply Nat.dvd_mul_right
    have contra:= Nat.dvd_trans o h
    absurd contra
    exact fact