import Mathlib

open Nat

theorem number_theory_4595_1 : 6! * 7! = 10! := by
  rw [show 7! = ascFactorial 7 4 by rfl]
  exact factorial_mul_ascFactorial 6 4

theorem number_theory_4587_2 : 10! = 7! * 5! * 3! := by
  rw [mul_assoc, mul_comm, show 5! * 3! = 6! by rfl]
  exact number_theory_4595_1

theorem number_theory_4587_3 : 16! = 14! * 5! * 2! := by
  rw [mul_assoc, show 5! * 2! = ascFactorial 15 2 by rfl]
  exact factorial_mul_ascFactorial 14 2

theorem number_theory_4587_4 : 9! = 7! * 3! * 3! * 2! := by
  native_decide