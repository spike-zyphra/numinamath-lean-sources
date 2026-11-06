import Mathlib

/- 2. At the parade of the royal musketeers, seeing that they could not be arranged in rows of 11 musketeers, D'Artagnan decided to arrange the musketeers in rows of 10 musketeers, but it turned out that there was one empty place in the last row. Then he tried to arrange them in rows of 9, 8, 7, 6, 5, 4, 3, 2 musketeers, but each time there was one empty place in the last row. Finally, the musketeers marched in a single file, which caused a burst of laughter among the spectators. Determine how many musketeers participated in the parade, given that there were no more than 7000. -/
theorem number_theory_240305 {n : ℕ} (hn : n ≤ 7000) (h1 : ¬ 11∣n) (h2 : n % 10 = 9)
  (h3 : n % 9 = 8) (h4 : n % 8 = 7) (h5 : n % 7 = 6) (h6 : n % 6 = 5) (h7 : n % 5 = 4)
  (h8 : n % 4 = 3) (h9 : n % 3 = 2) (h10 : n % 2 = 1) :
  n = 5039 := by {
  -- the LCM of all numbers from 2 to 10 is 2520
  have h2520: 2520 = Nat.lcm 2 
                    (Nat.lcm 3
                    (Nat.lcm 4
                    (Nat.lcm 5
                    (Nat.lcm 6
                    (Nat.lcm 7
                    (Nat.lcm 8
                    (Nat.lcm 9
                    10))))))):= by {
    norm_num
  }
  -- n+1 is divisible by all numbers from 2 to 10, so it is divisible by 2520
  have hn1: 2520∣(n+1) := by {
    rw [h2520]
    repeat (apply Nat.lcm_dvd _)
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h2]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h3]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h4]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h5]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h6]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h7]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h8]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h9]
    rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h10]
  }
  -- say n + 1 = 2520 * k
  cases hn1 with | intro k hk =>
  match k with 
  -- n+1 > 0, so k is not zero
  |0 => simp at hk
  -- if k = 1, then 11|n
  |1 => {
    simp at hk
    by_contra
    apply h1
    rw [hk]
    norm_num
  }
  -- k = 2 is the answer
  |2 => simp at hk; exact hk
  -- if k > 3, n > 7000 
  |k + 3 => {
    rw [mul_add] at hk
    simp at hk
    by_contra
    revert hn
    rw [hk]
    simp
  }
}