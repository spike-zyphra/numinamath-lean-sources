import Mathlib

/-Let $R$ be an integer base, $R \ge 2$. We are looking for digits $A, B, C, D$ in base $R$,
i.e., integers such that $0 \le A < R$, $0 \le B < R$, $0 \le C < R$, $0 \le D < R$.
We also require $A \neq 0$ (so that $\overline{AB}_R$ is a two-digit number) and
$C \neq 0$ (so that $\overline{CCBBDDCA}_R$ is an eight-digit number).
The digits must satisfy the equation $A^{(R \cdot A + B)} = N$,
where $N$ is the number represented by the sequence of digits $C, C, B, B, D, D, C, A$ in base $R$.
That is, $N = C \cdot R^7 + C \cdot R^6 + B \cdot R^5 + B \cdot R^4 + D \cdot R^3 + D \cdot R^2 + C \cdot R^1 + A \cdot R^0$.
This can be written as $A^{(R \cdot A + B)} = C \cdot (R^7 + R^6 + R) + B \cdot (R^5 + R^4) + D \cdot (R^3 + R^2) + A$.
Show that for $R=10$, the unique solution satisfying these conditions is $A=2, B=5, C=3, D=4$.-/

theorem number_theory_639659 (R A B C D: ℕ) (h1: R = 10) (h2: A ^ (R * A + B) = C * (R ^ 7 + R ^ 6 + R) + B * (R ^ 5 + R ^ 4) + D * (R ^ 3 + R ^ 2) + A)
  (h3: A ≠ 0) (h4: C ≠ 0) (h5: 0 ≤ A ∧ A < R) (h6: 0 ≤ B ∧ B < R) (h7: 0 ≤ C ∧ C < R) (h8: 0 ≤ D ∧ D < R):
  A = 2 ∧ B = 5 ∧ C = 3 ∧ D = 4 := by

  simp [h1] at *
  have lA: A < 3 := by
    by_contra! l
    have u: 3 ^ 30 ≤ A ^ (10 * A + B) := by
      suffices 3 ^ 30 ≤ A ^ (10 * A) by
        have v: A ^ (10 * A) ≤ A ^ (10 * A + B) := by
          apply Nat.pow_le_pow_right
          omega
          omega
        linarith
      suffices 3 ^ 30 ≤ A ^ 30 by
        have v: A ^ 30 ≤ A ^ (10 * A) := by
          apply Nat.pow_le_pow_right
          omega
          omega
        linarith
      apply Nat.pow_le_pow_left
      omega
    rw [h2] at u
    clear h2
    omega

  -- then A must be 2
  have va: A = 2 := by
    suffices A ≠ 1 by
      omega
    by_contra! o
    simp [o] at h2
    omega
  simp [va] at *

  have lb: 3 < B := by
    by_contra! l
    have u: 2 ^ (20 + B) ≤ 2 ^ 23 := by
      apply Nat.pow_le_pow_right
      omega
      omega
    rw [h2] at u
    omega
  have rb: B < 7 := by
    by_contra! l
    have u: 2 ^ 27 ≤ 2 ^ (20 + B) := by
      apply Nat.pow_le_pow_right
      omega
      omega
    rw [h2] at u
    omega
  interval_cases B

  -- B = 4
  .
    omega

  -- B = 5
  .
    omega

  -- B = 6
  .
    omega