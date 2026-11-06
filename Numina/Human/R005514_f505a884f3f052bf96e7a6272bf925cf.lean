import Mathlib

/- 
Question: What is the probability that the first card he throws down and the last card he throws down are the same color? Answer: 4/9
-/
theorem combinatorics_608583 
    (r b : ℕ) 
    (Red : r = 5) 
    (Blue : b = 5) 
    (All_Red : ar = (Nat.choose r 1) * (Nat.choose (r-1) 1))
    (All_Blue: ab = (Nat.choose b 1) * (Nat.choose (b-1) 1)):
    (ar + ab) * (r + b - 2).factorial / (r + b).factorial = (4 / 9: ℝ) := by

  -- Simplify combinatorial terms using choose(n,1) = n
  simp_all [Nat.choose_one_right]

  -- Compute factorial values for specific numbers to simplify arithmetic
  have h₁ : Nat.factorial 8 = 40320 := by decide
  have h₂ : Nat.factorial 10 = 3628800 := by decide

  -- Substitute the computed factorials into the expression
  rw [h₁ , h₂]

  -- Normalize the arithmetic expression to verify the result
  ring_nf

  