import Mathlib

theorem algebra_254856 {a b c : ℂ} (h : 1 + c + c ^ 2 = 0) :
    (a * c ^ 2 + b * c) * (b * c ^ 2 + a * c) = a ^ 2 - a * b + b ^ 2 := by
  have hc2 : c ^ 2 = -1 - c := by
    have eq1 : c ^ 2 = -1 - c := by
      have eq2 : c ^ 2 + 1 + c = 0 := by 
        calc
          c ^ 2 + 1 + c = (1 + c + c ^ 2) := by ring
          _ = 0 := by 
            simpa using h
      have eq3 : c ^ 2 = -1 - c := by
        calc
          c ^ 2 = (c ^ 2 + 1 + c) - 1 - c := by ring
          _ = 0 - 1 - c := by rw [eq2]
          _ = -1 - c := by ring
      exact_mod_cast eq3
    exact_mod_cast eq1
  have hc3 : c ^ 3 = 1 := by
    calc
      c ^ 3 = c * c ^ 2 := by ring
      _ = c * (-1 - c) := by rw [hc2]
      _ = -c - c ^ 2 := by ring
      _ = -c - (-1 - c) := by rw [hc2]
      _ = 1 := by ring
  have hc4 : c ^ 4 = c := by 
    calc
      c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ = (-1 - c) ^ 2 := by rw [hc2]
      _ = 1 + 2 * c + c ^ 2 := by ring
      _ = 1 + 2 * c + (-1 - c) := by rw [hc2]
      _ = c := by ring
  have h1 : (a * c ^ 2 + b * c) * (b * c ^ 2 + a * c) = 
          a * b * c ^ 4 + a^2 * c^3 + b^2 * c^3 + a * b * c^2 := by 
    ring_nf
  rw [h1]
  rw [hc4, hc3]
  rw [hc2]
  ring_nf