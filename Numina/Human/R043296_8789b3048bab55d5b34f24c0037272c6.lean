import Mathlib
/- Find the ordered quadruple of digits $(A, B, C, D)$, with $A>B>C>D$, such that

$$
\begin{aligned}
& A B C D \\
- & D C B A \\
= & B D A C .
\end{aligned}
$$ -/
theorem number_theory_611220 (A B C D : ℕ) (hA : 0 ≤ A ∧ A ≤ 9) (hB : 0 ≤ B ∧ B ≤ 9) (hC : 0 ≤ C ∧ C ≤ 9) (hD : 0 ≤ D ∧ D ≤ 9) (h : A > B ∧ B > C ∧ C > D) (h1 : A * 10 ^ 3 + B * 10 ^ 2 + C * 10 ^ 1 + D * 10 ^ 0 - (D * 10 ^ 3 + C * 10 ^ 2 + B * 10 ^ 1 + A * 10 ^ 0) = B * 10 ^ 3 + D * 10 ^ 2 + A * 10 ^ 1 + C * 10 ^ 0) : (A, B, C, D) = (7, 6, 4, 1):= by
  -- Simplify the equation in h1
  simp at h1
  -- Unpack the bounds for each digit
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  rcases hD with ⟨hD1, hD2⟩
  -- Unpack the ordering constraints
  rcases h with ⟨g1, g2, g3⟩
  -- Rewrite the equation in a more convenient form
  replace h1 : A * 1000 + B * 100 + C * 10 + D = B * 1000 + D * 100 + A * 10 + C + (D * 1000 + C * 100 + B * 10 + A):= by omega
  simp
  -- Derive a relationship between A, D and B
  have h2 : A = D + B:= by
    omega
  -- Derive a relationship between A, C and D
  have h3 : D + 10 = A + C:= by
    omega
  -- Substitute the value of A
  subst A
  simp at g1
  -- Derive a relationship between C, D and B
  have h4 : C + 9 = D + 2 * B:= by
    omega
  -- Simplify the equation using ring normalization
  ring_nf at h1
  -- Prove that (A,B,C,D) = (7,6,4,1)
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    omega
