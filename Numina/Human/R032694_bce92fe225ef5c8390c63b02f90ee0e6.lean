import Mathlib

/- Integers x and y with x > y > 0 satisfy x + y + xy = 80. What is x? -/
theorem algebra_96450 {x y : ℕ} (hx : 0 < y) (hy : y < x) (h : x + y + x * y = 80) : x = 26 := by
  -- show that (x+1) * (y+1) = 81
  have h : (x+1) * (y+1) = 81 := by linarith
  -- divisors of 81 are 1, 3, 9, 27, 81
  have hx' : (x+1) ∈ (81).divisors := by simp; use (y+1); rw [h]
  simp [show (81 : ℕ).divisors = {1, 3, 9, 27, 81} from rfl] at hx'
  -- try all cases to find that most are contradictory and only x = 26 works
  obtain hx' | hx' | hx' | hx' | hx' := hx'
  all_goals rw [hx'] at h
  all_goals linarith