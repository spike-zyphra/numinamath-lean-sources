import Mathlib

open Finset BigOperators

/- 定义函数`f`；我们不妨将`f`延拓为`ℕ → ℕ`的函数，并赋值`f 0 = 2`，
这样`exercise2`中的结论在`n = 0`时仍然满足。-/
def f_4530 : ℕ → ℕ
| 0 => 2
| 1 => 1
| 2 => 5
| n + 3 => f_4530 (n + 2) + 2 * f_4530 (n + 1)

theorem number_theory_4530 (n : ℕ) : (f_4530 n : ℤ) = 2 ^ n + (-1) ^ n := by
  match n with
  | 0 =>
    simp [f_4530]
  | 1 =>
    simp [f_4530]
  | 2 =>
    simp [f_4530]
  | n + 3 =>
    have h1 : (f_4530 (n + 2) : ℤ) = 2 ^ (n + 2) + (-1) ^ (n + 2) := by
      apply number_theory_4530
    have h2 : (f_4530 (n + 1) : ℤ) = 2 ^ (n + 1) + (-1) ^ (n + 1) := by
      apply number_theory_4530
    simp [f_4530] at *
    rw [h1, h2]
    ring_nf