import Mathlib

def lucas (n : ℕ) : ℕ := match n with
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

theorem number_theory_16187 : lucas (lucas 10) % 10 = 4 := by 
  norm_num [lucas]