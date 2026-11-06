import Mathlib

/- If $a,b,c$ are positive three real  numbers such that $| a-b | \geq c , | b-c | \geq a, | c-a | \geq b$ . Prove that one of $a,b,c$ is equal to the sum of the other two. -/
theorem inequalities_67332 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : abs (a - b) ≥ c) (h2 : abs (b - c) ≥ a) (h3 : abs (c - a) ≥ b) :
    a = b + c ∨ b = a + c ∨ c = a + b := by 
  cases' abs_cases (a - b) with h h <;>
  cases' abs_cases (b - c) with h' h' <;>
  cases' abs_cases (c - a) with h'' h'' <;>
  linarith