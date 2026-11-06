import Mathlib

def D: ℕ → ℕ
  | 0 => 3  -- Thursday
  | 1 => 4 -- Friday
  | 2 => 5 -- Saturday
  | 3 => 6 -- Sunday
  | 4 => 0 -- Monday
  | 5 => 1 -- Tuesday
  | 6 => 2 -- Wednesday
  | _ => 0 -- Default case, not used

/-Let $N$ be a positive integer. If today is Thursday,
determine the day of the week it will be $N$ days later.
Show that this day is $D_k$ where $k = N \pmod 7$ and $(D_0, D_1, D_2, D_3, D_4, D_5, D_6)$ represents the sequence of days
(Thursday, Friday, Saturday, Sunday, Monday, Tuesday, Wednesday).
-/

theorem number_theory_640926 (k N: ℕ) (h: k = N % 7): (D 0 + N) % 7 = D k := by

  rw [Nat.add_mod]
  rw [h]
  clear h
  set s:= N % 7
  have ls: s < 7 := by
    omega
  interval_cases s
  all_goals simp [D]
