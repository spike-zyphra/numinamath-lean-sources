import Mathlib

def dot (n : ℕ) : ℕ := match n with
| 0 => 1
| n + 1 => if Even n then (dot n) * 2 else (dot n)

theorem number_theory_269104 : dot 25 = 8192 := by
  native_decide  -- This handles the concrete computation