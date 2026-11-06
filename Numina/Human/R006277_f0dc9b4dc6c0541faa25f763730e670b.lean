import Mathlib

/- Let $A, B, C$ be digits in base 6, where $A \neq 0$. A number $N$ is written in base 6 as $\overline{ABC}_6$, which means $N = A \cdot 6^2 + B \cdot 6 + C$. If $N = B^C - A$, find all such numbers $N$. Show that the only solution is $N = \overline{143}_6$.
(Note: $\overline{143}_6$ is $1 \cdot 6^2 + 4 \cdot 6 + 3 = 36 + 24 + 3 = 63$ in base 10. The condition is $63 = 4^3 - 1 = 64 - 1 = 63$.) -/
theorem number_theory_635459 :
    {(N) | (A : ℕ) (B : ℕ) (C : ℕ) (N : ℕ) (_ : A < 6) (_ : B < 6) (_ : C < 6) (_ : A ≠ 0) (_ : N = A * 6 ^ 2 + B * 6 + C) (_ : (N : ℤ) = B ^ C - A)} = {63} := by
  -- We show that the only solution is $N = \overline{143}_6$.
  ext N
  simp
  constructor
  -- We first show that $N = \overline{143}_6$ is a solution.
  swap
  . rintro rfl
    use 1, 4, 3, 63
    norm_num
  -- We now show that any solution must be $N = \overline{143}_6$.
  . rintro ⟨A, B, C, N, h₁, h₂, h₃, h₄, h₅, h₆, rfl⟩
    subst h₂
    revert h₃ h₁
    -- We quantify over the digits.
    revert C
    revert B
    revert A
    -- We check every possible value of $A$, $B$, and $C$.
    native_decide