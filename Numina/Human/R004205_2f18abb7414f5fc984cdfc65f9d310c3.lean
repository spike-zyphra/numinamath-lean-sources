import Mathlib
/-2. The father divided a certain amount of money among his children in the following order. To the eldest son, he gave 1000 denars and $\frac{1}{8}$ of the remaining money, to the second child, he gave 2000 denars and $\frac{1}{8}$ of the new remainder, to the third child, he gave 3000 denars and $\frac{1}{8}$ of the new remainder, and so on until the last child. In this way, the entire sum of money was divided, and each child received an equal share. How much money did he give to each of the children, and how many children did he have?-/
theorem algebra_242561 (x n1 n2 n : ℝ )
(h1 : n1 = 1000 + ( x - 1000 ) / 8)
(h2 : n2 = 2000 + ( x - n1 - 2000) / 8)
(heq : n1 = n2)
(hn : n = x / n1):
x = 49000 ∧ n =7 := by
-- Step 1: Rewrite the equation using the equality
  rw [←heq] at h2

  -- Step 2: Apply the first equation to the rewritten equation
  rw [h1] at h2

  -- Step 3: Simplify the equation
  field_simp at h2

  -- Step 4: Calculate the value of x
  have xval : x = 49000 := by
    linarith

  -- Step 5: Apply the calculated value of x to the first equation
  rw [xval] at h1

  -- Step 6: Calculate the value of n
  have nval : n = 7 := by
    rw [xval,h1] at hn
    linarith

  -- Step 7: Return the calculated values of x and n
  exact ⟨xval, nval⟩