import Mathlib

/- If $x$ and $y$ are positive integers for which $3x + 2y + xy = 115$, then what is $x + y$? -/
theorem algebra_19979 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : 3 * x + 2 * y + x * y = 115) : x + y = 17 := by
  -- Add 6 to both sides of the equation
  apply_fun (· + 6) at h
  -- Rewrite the equation, and we get (x + 2) * (y + 3) = 121
  replace h : (x + 2) * (y + 3) = 121 := by linarith only [h]
  -- We have x + 2 ∣ 121
  have k : x + 2 ∣ 121 := ⟨y + 3, h.symm⟩
  -- Thus, x + 2 is a divisor of 121
  replace k : x + 2 ∈ Nat.divisors 121 := Nat.mem_divisors.2 ⟨k, by simp⟩
  -- 121 has 3 divisors: 1, 11, 121
  -- The decide tactic is used to prove that 121 has 3 divisors: 1, 11, 121, which can be done by hand.
  have l : Nat.divisors 121 = {1, 11, 121} := by decide
  -- Thus, x + 2 is either 1, 11, or 121
  rw [l] at k
  -- x is either 9 or 119
  simp at k
  -- Case analysis
  rcases k with rfl | rfl
  all_goals
    omega
