import Mathlib

theorem number_theory_195964 :
    ∃ a b, a + b = 987654321 ∧
      (Nat.digits 10 a).length = 9 ∧
      (Nat.digits 10 b).length = 9 ∧
      (Nat.digits 10 a).toFinset = (Nat.digits 10 b).toFinset := by

  use 123456789, 864197532

  all_goals norm_num
  <;> native_decide