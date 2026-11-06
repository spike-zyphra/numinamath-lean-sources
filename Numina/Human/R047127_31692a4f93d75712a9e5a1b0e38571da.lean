import Mathlib
/-- Each piece of candy in a store costs a whole number of cents. Casper has exactly enough money to buy either $12$ pieces of red candy, $14$ pieces of green candy, $15$ pieces of blue candy, or $n$ pieces of purple candy. A piece of purple candy costs $20$ cents. What is the smallest possible value of $n$?

$\textbf{(A) } 18 \qquad \textbf{(B) } 21 \qquad \textbf{(C) } 24\qquad \textbf{(D) } 25 \qquad \textbf{(E) } 28$ -/
theorem number_theory_93352 : IsLeast {n | ∃ a b c, a > 0 ∧ b > 0 ∧ c > 0 ∧ 12 * a = 14 * b ∧ 14 * b = 15 * c ∧ 15 * c = n * 20} 21 := by
  -- https://artofproblemsolving.com/wiki/index.php/2019_AMC_10B_Problems/Problem_7
  constructor
  -- witnesses
  · exists 35, 30, 28
  · intros n n1
    obtain ⟨a, b, c, d, e, f, g, h, i⟩ := n1
    -- algebraic manipulation concludes the goal
    omega