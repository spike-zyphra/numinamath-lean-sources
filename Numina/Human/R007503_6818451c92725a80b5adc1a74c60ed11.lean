import Mathlib

/-Let $N$ be the largest integer whose square has exactly $3$ digits when written in base 9.

What is $N$, expressed in base 9?-/
theorem number_theory_15276  :
  IsGreatest {n | 9^2 ≤ n^2 ∧ n^2 < 9^3} 26 ∧ 26 = Nat.ofDigits 9 [8, 2] := by
    constructor
    -- First, we prove N = 26 in base 10. 
    · constructor
      · simp
      · -- $n^2$ has exactly $3$ digits in base 9 if and only if $$9^2\le n^2<9^3.
        intro a ha
        simp at ha
        -- So, $N=3^3-1=3\cdot 9-1 =2\cdot 9+8.$
        nlinarith
    · -- Then, we prove 26 is represented as 28 in base 9.
      exact rfl
