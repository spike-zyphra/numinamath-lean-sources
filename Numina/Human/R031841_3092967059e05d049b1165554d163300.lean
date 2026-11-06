import Mathlib
/-- Two farmers agree that pigs are worth $300$ dollars and that goats are worth $210$ dollars. When one farmer owes the other money, he pays the debt in pigs or goats, with "change" received in the form of goats or pigs as necessary. (For example, a $390$ dollar debt could be paid with two pigs, with one goat received in change.) What is the amount of the smallest positive debt that can be resolved in this way?

$\textbf{(A) } 5\qquad \textbf{(B) } 10\qquad \textbf{(C) } 30\qquad \textbf{(D) } 90\qquad \textbf{(E) } 210$ -/
theorem number_theory_96211 : IsLeast {x | 0 < x ∧ ∃ (a b : ℤ), x = 300 * a + 210 * b} 30 := by
  constructor
  -- (-2, 3) is a witness
  · simp only [Set.mem_setOf_eq, Nat.ofNat_pos, true_and]
    exists -2
    exists 3
  · rw [mem_lowerBounds]
    simp only [Set.mem_setOf_eq, and_imp, forall_exists_index]
    intros x hx x1 x2 h3
    -- Bezout's Lemma tells us that the smallest $c$ for the Diophantine equation $am + bn = c$ to have solutions is when $c$ is the GCD (greatest common divisor) of $a$ and $b$. Therefore, the answer is $gcd(300,210)=\boxed{\textbf{(C) }30}.$
    omega