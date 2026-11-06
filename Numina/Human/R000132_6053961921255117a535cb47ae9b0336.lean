import Mathlib

open Finset

/- a) The binary number \( (101110110)_{2} \) is divisible by 5.-/
theorem number_theory_4753_1 {a : List ℕ} (ha : a = [0, 1, 1, 0, 1, 1, 1, 0, 1]) :
    ¬5 ∣ ∑ i ∈ range a.length, a[i]! * 2^i := by
  -- verify by computation
  rw [ha]
  simp [sum_range_succ]
  norm_num

/- b) The ternary number \( (12100122)_{3} \) is divisible by 2, and whether it is divisible by 5.-/
theorem number_theory_4753_2 {a : List ℕ} (ha : a = [2, 2, 1, 0, 0, 1, 2, 1]) :
    ¬2 ∣ ∑ i ∈ range a.length, a[i]! * 3^i ∧
    5 ∣ ∑ i ∈ range a.length, a[i]! * 3^i := by
  -- verify by computation
  rw [ha]
  simp [sum_range_succ]
  norm_num

/- c) The octal number \( (364701244)_{8} \) is divisible by 5, and whether it is divisible by 13.-/
theorem number_theory_4753_3 {a : List ℕ} (ha : a = [4, 4, 2, 1, 0, 7, 4, 6, 3]) :
    ¬5 ∣ ∑ i ∈ range a.length, a[i]! * 8^i ∧
    ¬13 ∣ ∑ i ∈ range a.length, a[i]! * 8^i := by
  -- verify by computation
  rw [ha]
  simp [sum_range_succ]
  norm_num

/- d) The decimal number \( (5837041320219)_{10} \) is divisible by 101.-/
theorem number_theory_4753_4 {a : List ℕ} (ha : a = [9, 1, 2, 0, 2, 3, 1, 4, 0, 7, 3, 8, 5]) :
    101 ∣ ∑ i ∈ range a.length, a[i]! * 10^i := by
  -- verify by computation
  rw [ha]
  simp [sum_range_succ]
  norm_num
