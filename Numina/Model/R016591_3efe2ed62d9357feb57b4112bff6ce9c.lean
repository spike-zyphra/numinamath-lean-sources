import Mathlib

theorem number_theory_280761 (p : ℕ) (hp : Odd p ∧ Nat.Prime p)
    (k : ℕ) (hk : ∃ m : ℕ, 0 < m ∧ m^2 = k - p * k) :
    k = ((p + 1)^2) / 4 := by
  rcases hk with ⟨m, hm, heq⟩
  exfalso
  have heq1 : k ≤ p * k := by
    have hp12 : p ≥ 1 := by 
      have hp5 := hp.right
      have : p ≥ 2 := Nat.Prime.two_le hp5
      linarith
    nlinarith [show k ≥ 0 by omega, hp12]
  -- k - p * k = 0 because $k \cdot (1 - p)$ is negative
  have heq2 : k - p * k = 0 := by
    omega
  rw [heq2] at heq
  -- We established from above analysis that $k \geq 0$. Since $p \cdot k \geq k$
  -- which implies $0 \cdot m^2 = k - p \cdot k$, now $m > 0$ implies $0 > 0$.
  have eq1 : m ^ 2 = (0 : ℕ) := by 
    omega 
  have h3 : m = 0 := by
    nlinarith
  linarith