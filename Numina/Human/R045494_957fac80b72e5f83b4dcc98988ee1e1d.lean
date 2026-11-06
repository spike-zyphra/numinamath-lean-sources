import Mathlib

/- Prove that the remainder of dividing the square of an integer by $3$ is different from $2$. -/
theorem number_theory_47025 (n : ℤ) : ¬n^2 ≡ 2 [ZMOD 3] := by 
  have h₁ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  -- Consider the possible remainders for n with respect to 3.
  -- Knowing n % 3 = {0, 1, 2}, we examine all n^(2) modulo behavior.
  rcases h₁ with (h₁ | h₁ | h₁) <;> simp [h₁, pow_two, Int.ModEq, Int.mul_emod]