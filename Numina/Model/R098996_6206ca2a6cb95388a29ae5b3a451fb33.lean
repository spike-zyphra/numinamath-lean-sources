import Mathlib

theorem algebra_300818 {a : ℂ} (ha : a^2 + a + 1 = 0) :
    a^1992 + a^322 + a^2 = 0 := by
  have h1 : a^2 = -a - 1 := by
    have eq1 : a^2 = -a - 1 := by
      calc 
        a^2 = a^2 + a + 1 - a - 1 := by ring_nf
        _ = 0 - a - 1 := by rw [ha]
        _ = -a - 1 := by ring
    exact eq1
  
  have h2 : a^3 = 1 := by
    calc
      a^3 = a * a^2 := by ring_nf
      _ = a * (-a - 1) := by rw [h1]
      _ = -a^2 - a := by ring_nf
      _ = -(-a - 1) - a := by rw [h1]
      _ = 1 := by ring_nf
  
  have h3 : a^1992 = 1 := by
    calc
      a^1992 = (a^3) ^ 664 := by ring_nf
      _ = 1 ^ 664 := by rw [h2]
      _ = 1 := by norm_num

  have h4 : a^322 = a := by
    calc
      a^322 = (a^3) ^ 107 * a := by ring_nf
      _ = 1 ^ 107 * a := by rw [h2]
      _ = 1 * a := by simp
      _ = a := by ring_nf
  
  rw [h3, h4, h1]
  ring_nf