import Mathlib

theorem algebra_229043 {a : ℂ} (ha : a^2 + a + 1 = 0) :
    a^1987 + 1 / a^1987 = -1 := by
  have ha1 : a ≠ 0 := by 
    by_contra h
    rw [h] at ha
    norm_num at ha 
  have eq1 : a^2 = -a - 1 := by 
    calc 
      a^2 = a^2 + a + 1 - a - 1 := by ring
      _ = (-a -1) := by
        rw [show a^2 + a + 1 = 0 by exact_mod_cast ha]
        all_goals ring
  have eq2 : a ^ 3 = 1 := by
    calc 
      a ^ 3 = a * a ^ 2 := by ring
      _ = a * (-a - 1) := by rw [eq1]
      _ = -a^2 - a := by ring
      _ = -(-a -1) - a := by rw [eq1]
      _ = 1 := by ring
  have eq3 : a^1987 = a := by 
    calc 
      a^1987 = a^(3 * 662 + 1) := by norm_num 
      _ = (a^3)^662 * a := by ring
      _ = (1)^662 * a := by rw [eq2]
      _ = 1^662 * a := by rfl 
      _ = a := by norm_num 
  have eq5 : 1 / a^1987 = a^2 := by
    rw [eq3]
    field_simp [ha1]
    <;> 
    rw [← eq2] 
    <;> ring
  rw [eq5, eq3]
  have eq6 : a + a^2 = -1 := by 
    have eq7 : a^2 + a + 1 = 0 := by 
      exact_mod_cast ha 
    calc 
      a + a^2 = (a^2 + a + 1) - 1 := by ring
      _ = (0) - 1 := by 
        rw [eq7]
      _ = -1 := by ring
  calc
    a + a ^ 2 = a + a ^ 2 := by ring
    _ = -1 := by 
      have eq7 : a + a ^ 2 = -1 := eq6 
      exact_mod_cast eq7