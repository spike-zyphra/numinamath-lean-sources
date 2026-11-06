import Mathlib

open Finset BigOperators

/- 定义函数`f`；我们不妨将`f`延拓为`ℕ → ℕ`的函数，并赋值`f 0 = 2`，
这样`exercise2`中的结论在`n = 0`时仍然满足。-/
def f_4530 : ℕ → ℕ
| 0 => 2
| 1 => 1
| 2 => 5
| n + 3 => f_4530 (n + 2) + 2 * f_4530 (n + 1)

/- We define a function recursively for all positive integers \( n \) by \( f(1) = 1 \), \( f(2) = 5 \),
  and for \( n > 2 \), \( f(n+1) = f(n) + 2 f(n-1) \). Show that \( f(n) = 2^{n} + (-1)^{n} \),
  using the second principle of mathematical induction. -/
theorem number_theory_4530 (n : ℕ) : (f_4530 n : ℤ) = 2 ^ n + (-1) ^ n :=
  -- 使用第二数学归纳法证明结论。这里我们使用Lean的停机检查器(termination checker)
  -- 来保证我们在证明结论对`n`成立时，只使用了结论对`< n`的自然数成立作为假设。
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by
    have h : (f_4530 (n + 1) : ℤ) = 2 ^ (n + 1) + (-1) ^ (n + 1) := number_theory_4530 (n + 1)
    have h' : (f_4530 (n + 2) : ℤ) = 2 ^ (n + 2) + (-1) ^ (n + 2) := number_theory_4530 (n + 2)
    rw [f_4530]
    push_cast
    rw [h, h']
    by_cases ev : Even n
    · simp [pow_add, ev]; ring
    · simp [pow_add, ev]; ring
