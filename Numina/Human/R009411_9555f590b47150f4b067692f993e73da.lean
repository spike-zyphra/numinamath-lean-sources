import Mathlib
/-- Ed and Ann both have lemonade with their lunch. Ed orders the regular size. Ann gets the large lemonade, which is 50% more than the regular. After both consume $\frac{3}{4}$ of their drinks, Ann gives Ed a third of what she has left, and 2 additional ounces. When they finish their lemonades they realize that they both drank the same amount. How many ounces of lemonade did they drink together?

$\textbf{(A)}\ 30\qquad\textbf{(B)}\ 32\qquad\textbf{(C)}\ 36\qquad\textbf{(D)}\ 40\qquad\textbf{(E)}\ 50$ -/
theorem algebra_96405 (x : ℝ) (hx : x > 0) (h : (1 + 50 / 100) * x * (3 / 4) + 2 = x * (3 / 4)) :
x = 40 := by
  -- In the end, Ed drank everything in his original lemonade plus what Ann gave him, and Ann drank everything in her original lemonade minus what she gave Ed. Thus we have\[x + \frac{x}{8} + 2 = \frac{3x}{2} - \frac{x}{8} - 2\]
  -- The total amount the two of them drank is simply
  -- \[x + \frac{3}{2}x = 16 + 24 = \boxed{\textbf{(D)}\ 40}\]
  linarith