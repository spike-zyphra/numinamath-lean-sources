import Mathlib

theorem number_theory_263185 (x : ℤ) (h : Even (3 * x + 1)) : Odd (7 * x + 4) := by
  obtain ⟨k, hk⟩ := h 
  have h1 : 3 * x = 2 * k - 1 := by linarith
  have h2 : x % 2 = 1 := by 
    have h3 : (3 * x) % 2 = 1 := by 
      omega
    have : x % 2 = 1 := by 
      omega
    assumption 
  have hx : Odd x := by 
    refine ⟨(x - 1) / 2, by omega⟩ 
  obtain ⟨m, hm⟩ := hx 
  use 7 * m + 5 
  linarith [show x = 2 * m + 1 by linarith]