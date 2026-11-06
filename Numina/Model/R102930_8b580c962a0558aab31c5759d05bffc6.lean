import Mathlib

theorem algebra_290 {n m : ℕ} {x : ℚ}
(hn : n ≠ 0) (hm : m ≠ 0) (h : (1 : ℚ) / 4 * n = (2 : ℚ) / 3 * m) (h' : x = (1 : ℚ) / 4 * n + (2 : ℚ) / 3 * m) :
    x / (n + m) = 4 / 11 := by
  have eq1 : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have eq2 : (m : ℚ) ≠ 0 := by exact_mod_cast hm

  have eq3 : (x : ℚ) = (4 / 3 : ℚ) * (m : ℚ) := by 
    rw [h']
    have eq4 : (1 : ℚ) / 4 * (n : ℚ) = (2 : ℚ) / 3 * (m : ℚ) := by linarith [h]
    linarith [eq4]

  -- From h: (1 : ℚ) / 4 * n = (2 : ℚ) / 3 * m, solve for n + m
  have eq6 : (n : ℚ) = (8 / 3 : ℚ) * (m : ℚ) := by 
    linarith [h]
  
  have eq7 : (n : ℚ) + (m : ℚ) = (11 / 3 : ℚ) * (m : ℚ) := by 
    linarith [eq6]

  rw [eq3]
  rw [eq7]

  -- Simplify
  have eq8 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  field_simp [eq8]
  <;> ring