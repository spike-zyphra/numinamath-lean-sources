import Mathlib
/- Let $C$ be a positive integer. Find the remainder when $29^{3C}$ is divided by $13$. Show the answer is 1. -/
theorem number_theory_638442 (C : ℕ) (hC : C > 0) : 29 ^ (3 * C) ≡ 1 [MOD 13]:= by
  -- Rewrite the expression using the properties of modular arithmetic
  rw [show 29 ^ (3 * C) = (29 ^ 3) ^ C by exact Nat.pow_mul 29 3 C]
  simp
  have g1 : 24389 ≡ 1 [MOD 13]:= by rfl
  -- Use the properties of modular arithmetic to simplify the expression
  replace g1 : 24389 ^ C ≡ 1 ^ C [MOD 13]:= by exact Nat.ModEq.pow C g1
  simp at g1
  exact g1
