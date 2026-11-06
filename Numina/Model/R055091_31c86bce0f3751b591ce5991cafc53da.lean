import Mathlib

theorem algebra_211098 (A B C D : ℕ) (h₀ : A ≠ 0) (h₁ : B ≠ 0)
    (h₂ : C ≠ 0) (h₃ : D ≠ 0) (h₄ : ¬(A = 9)) (h₅ : ¬(B = 9))
    (h₆ : ¬(C = 9)) (h₇ : ¬(D = 9)) (h₈ : ∃ x, A * x ^ 2 + B * x + B * 10 = 0)
    (h₉ : ∃ x, A * x ^ 2 + B * B * x + 10 = 0) (h₁₀ : ∃ x, A * B * x ^ 2 + B * x + 10 = 0) :
    (A = 1 ∧ B = 7 ∧ C = 1 ∧ D = 0) ∨ (A = 1 ∧ B = 8 ∧ C = 1 ∧ D = 0) := by
  rcases h₈ with ⟨x, hx⟩
  rcases h₉ with ⟨y, hy⟩
  rcases h₁₀ with ⟨z, hz⟩
  -- Use omega, which handles non-negative natural numbers well
  -- We reason about the constraints without negative roots
  -- Since x is a natural number, negative solutions are impossible
  -- Therefore, we only need to check positive roots

  -- If we have a quadratic with a natural root x, then:
  -- A * x^2 + B * x + B * 10 = 0 implies that root x is rational
  -- Either the discriminant is not divisible, or we find special small roots
  -- From the existence hypotheses, we need these quadratic to under-constrain
  -- Therefore, we only get specific digit combinations
  -- By manual calculation, we can verify the solutions
  have hA : A ≤ 8 := by
    omega
  have hB : B ≤ 8 := by
    omega
  -- Since A and B are small (digits from 1-8), it's feasible to try all possibilities
  interval_cases A <;> interval_cases B <;> omega