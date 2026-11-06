import Mathlib

/-
Let $b$ be a natural number such that $b \ge 2$. Let $n$ be a natural number (non-negative integer).
Show that $b^{3n+3} + 3 \cdot b^{2n+2} + 3 \cdot b^{n+1} + 1 = (b^{n+1}+1)^3$.
-/


lemma l1 (m:ℕ) : (m+1)^3 = m^3 + 3*m^2 + 3*m + 1 := by ring

theorem number_theory_636619 (b n:ℕ) (hb: 2 ≤ b):
b^(3*n+3) + 3* b^(2*n+2) + 3* b^(n+1) + 1  = (b^(n+1)+1)^3 := by 
  rw [l1]
  rw [← pow_mul]
  rw [← pow_mul]
  ring