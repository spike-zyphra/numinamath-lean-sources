import Mathlib

open Finset Real Nat

/- find the smallest positive integer n such that power tower n > 3^(3^(3^3))-/

theorem number_theory_609062:  (2^2^2^2^2^2 > 3^(3^(3^3))) ∧ (2^2^2^2^2 < 3^(3^(3^3))) := by
  have pt4: 2^2^2^2 = 65536 := by norm_num
  have ineq1: 2 ^ 65535 > 4 ^ 27 := by
    have o: 4 ^ 27 = 2 ^ 54 := by
      calc
        4 ^ 27 = (2 ^ 2) ^ 27 := by rw [show 4 = 2 ^ 2 by ring]
             _ = 2 ^ (2 * 27) := by rw [←Nat.pow_mul]
             _ = 2 ^ 54 := by rw [show 2 * 27 = 54 by ring]
    rw [o]
    rw [gt_iff_lt]
    apply Nat.pow_lt_pow_of_lt
    . omega
    . omega
  have ineq2: 4 ^ 2 ^ 65535 > 4 ^ (4 ^ 27) := by
    rw [gt_iff_lt]
    apply Nat.pow_lt_pow_of_lt
    . norm_num
    . rw [← gt_iff_lt]
      exact ineq1
  have ineq3: 4 ^ (4 ^ 27) > 3 ^ (4 ^ 27) := by
    rw [gt_iff_lt]
    rw [Nat.pow_lt_pow_iff_left]
    . norm_num
    . norm_num
  have ineq4: 3 ^ (4 ^ 27) > 3 ^ (3 ^ 27) := by
    rw [gt_iff_lt]
    apply Nat.pow_lt_pow_of_lt
    . norm_num
    . rw [Nat.pow_lt_pow_iff_left]
      . norm_num
      . norm_num
  have ineq5: 3^(3^(3^3)) > 3^(3^3) := by
    rw [gt_iff_lt]
    apply Nat.pow_lt_pow_of_lt
    . norm_num
    . norm_num
  have ineq6: 3^(3^(3^3)) > 65536 := by
    calc
      3^(3^(3^3)) > 3^(3^3) := by exact ineq5
                 _> 65536 := by norm_num
  have ineq7: 2 ^ 16 < 3 ^ 27 := by
    calc
      2 ^ 16 < 3 ^ 16 := by rw [Nat.pow_lt_pow_iff_left];norm_num;norm_num
           _ < 3 ^ 27 := by apply Nat.pow_lt_pow_of_lt; norm_num; norm_num
  let a:= 3^(3^(3^3))
  have ha: 3^(3^(3^3)) = a := by simp only [a]
  rw [ha]
  constructor
  . calc
      2 ^ 2 ^ 2 ^ 2 ^ 2 ^2 = 2 ^ 2 ^ 65536 := by rw [pt4]
                          _= 2 ^ 2 ^ (65535 + 1) := by rw [show 65536 = 65535 + 1 by norm_num]
                          _= 2 ^ (2 ^ 65535 * 2) := by rw [show 2 ^ (65535 + 1) = 2 ^ 65535 * 2 by rw [Nat.pow_add_one 2 65535]]
                          _= (2 ^ 2) ^ 2 ^ 65535 := by rw [Nat.pow_mul']
                          _= 4 ^ 2 ^ 65535 := by rw [show 4 = 2 ^ 2 by ring]
                          _> 4 ^ (4 ^ 27) := by exact ineq2
                          _> 3 ^ (4 ^ 27) := by exact ineq3
                          _> 3 ^ (3 ^ 27) := by exact ineq4
                          _= 3 ^ (3 ^ (3 ^ 3)) := by rw [show 27 = 3 ^ 3 by ring]
                          _= a := by rw [ha]
  .   calc
          2 ^ 2 ^ 2 ^ 2 ^ 2 = 2 ^ (2 ^ 16) := by rw [show 2 ^ 2 ^ 2 = 16 by ring]
                           _< 3 ^ (2 ^ 16) := by rw [Nat.pow_lt_pow_iff_left]; norm_num; norm_num
                           _< 3 ^ (3 ^ 27) := by apply Nat.pow_lt_pow_of_lt; norm_num; exact ineq7