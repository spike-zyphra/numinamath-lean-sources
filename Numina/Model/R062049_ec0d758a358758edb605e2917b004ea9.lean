import Mathlib

def periodicalCicadas : ℕ → ℕ
| 0 => 17
| 1 => 13
| _ => 0

theorem number_theory_4511 :
    lcm (periodicalCicadas 0) (periodicalCicadas 1) + 1900 = 2121 := by 
  calc 
    lcm (periodicalCicadas 0) (periodicalCicadas 1) + 1900 
        = lcm 17 13 + 1900 := by 
            simp [periodicalCicadas]
    _ = 221 + 1900 := by
      norm_num [lcm]
    _ = 2121 := by
      norm_num