import Mathlib

open Nat

/- For what digit $A$ is the numeral $1AA$ a perfect square in base-$5$ and a perfect cube in base-$6$?
$\text{(A) }0\qquad\text{(B) }1\qquad\text{(C) }2\qquad\text{(D) }3\qquad\text{(E) }4$ -/
theorem number_theory_58473 (A : ℕ) (h_A : A ≤ 4)
    (h_sq1 : IsSquare (Nat.ofDigits 5 [A, A, 1]))
    (h_sq2 : ∃ n, Nat.ofDigits 6 [A, A, 1] = n ^ 3) : A = 4 := by 
  have h₁ : A ≤ 4 := h_A
  have h₂ : IsSquare (Nat.ofDigits 5 [A, A, 1]) := h_sq1
  have h₃ : ∃ n, Nat.ofDigits 6 [A, A, 1] = n ^ 3 := h_sq2
  have h₄ : A = 4 := by
    -- We need to prove that $A = 4$. We'll check each possible value of $A$ ($0$ to $4$) to see if it satisfies both conditions.
    interval_cases A <;> norm_num [Nat.ofDigits_cons, Nat.ofDigits_singleton, 
    IsSquare, Nat.exists_mul_self, pow_two, pow_three] at h₂ h₃ ⊢ <;>   
    {
      rcases h₃ with ⟨n, hn⟩
      have h₄ : n ≤ 4 := by
        nlinarith
      interval_cases n <;> norm_num at hn ⊢ 
    } 
  exact h₄