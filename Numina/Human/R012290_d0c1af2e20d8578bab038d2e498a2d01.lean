import Mathlib

-- Letters A, B, C, and D represent four different digits selected from 0, 1, 2, …, 9. If (A+B)/(C+D) is an integer that is as large as possible, what is the value of A+B? (A) 13 (B) 14 (C) 15 (D) 16 (E) 17
theorem number_theory_93724 : IsGreatest {E | ∃ (A B C D:ℕ), A ≤ 9 ∧ B ≤ 9 ∧ C ≤ 9 ∧ D ≤ 9 ∧ A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧ ∃ (m : ℕ), m = ((A+B):ℚ)/(C+D) ∧ E = A + B} 17 := by
  constructor
  -- Checking to make sure the fraction is an integer, $\\frac{A+B}{C+D} = \\frac{17}{1} = 17$, and so the values are correct, and $A+B = 17$, giving the answer $\\boxed{E}$.
  · simp
    use 9
    simp
    use 8
    simp
    use 1
    simp
    use 0
    simp
    use 17
    norm_cast
  -- If we want $\\frac{A+B}{C+D}$ to be as large as possible, we want to try to maximize the numerator $A+B$ and minimize the denominator $C+D$. Picking $A=9$ and $B=8$ will maximize the numerator, and picking $C=0$ and $D=1$ will minimize the denominator.
  · intro E hE
    simp at hE
    rcases hE with ⟨A, hA, B, hB, C, hC, D, hD, h1, h2, h3, h4, h5, h6, ⟨m, hm⟩, heq⟩
    omega
