import Mathlib

theorem algebra_2458 (k : ℤ) (h : ∃ x : ℝ, 2*x*(k*x-4)-x^2+6=0) :
    k ≤ 1 := by
  rcases h with ⟨x, hx⟩
  have h_eq : (2 * (k : ℝ) - 1) * x ^ 2 - 8 * x + 6 = 0 := by
    have h1 : 2 * x * (k * x - 4) - x ^ 2 + 6 = 0 := by
      simpa using hx
    ring_nf at h1 ⊢
    linarith
  -- Derive the discriminant from the existence of a real root
  have h_discriminant : (8 : ℝ) ^ 2 - 4 * (2 * (k : ℝ) - 1) * 6 ≥ 0 := by
    nlinarith [sq_nonneg ((2 * (k : ℝ) - 1) * x - 4)]
  -- Simplify discriminant inequality
  ring_nf at h_discriminant
  -- Now we need to derive the bound on k
  have h' : (k : ℝ) ≤ (11 / 6 : ℝ) := by
    nlinarith
  -- Convert the real bound to integer constraint
  have h_k : k ≤ 1 := by
    by_contra h1
    push_neg at h1
    have h2 : k ≥ 2 := by omega
    have h3 : (k : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h2
    -- Contradiction arises because k must be <= 11/6 < 2
    linarith
  exact h_k