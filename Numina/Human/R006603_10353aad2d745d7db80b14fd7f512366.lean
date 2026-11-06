import Mathlib


-- Theorem: Let $p$ be a prime number and let $a$ be an integer. Suppose there exists an element $y_0 \in \mathbb{Z}_p$ (the ring of integers modulo $p$) such that $y_0^2 = -1$ in $\mathbb{Z}_p$.
-- Then for any $x \in \mathbb{Z}_p$, the equality $x^2 = -a^2$ holds in $\mathbb{Z}_p$ if and only if $x = (a \pmod p) y_0$ or $x = -(a \pmod p) y_0$.
-- (Note: $a \pmod p$ denotes the residue class of $a$ in $\mathbb{Z}_p$. If $a$ is already taken as an element of $\mathbb{Z}_p$, this is simply $a$.)

theorem number_theory_639044 {p a : ℕ} (hp : Nat.Prime p) (y0 : ZMod p) (hy0 : y0 ^ 2 = -1) :
  ∀ x : ZMod p, x ^ 2 = -a ^ 2 ↔  x = (a : ZMod p) * y0 ∨ x = -(a : ZMod p) * y0 := by 
  intro x 
  constructor
  · 
    intro h
    have eq1 : x ^ 2 = (a * y0) ^ 2 := by
      rw [h, mul_pow, hy0]
      simp
    have eq2 : (x - a * y0) * (x + a * y0) = 0 := by 
      ring_nf
      rw [eq1]
      ring
    have prime1 : Fact (Nat.Prime p) := by 
      exact { out := hp }
    -- since p is a prime number then ZMod p is a Domain, then x * y = 0 → x = 0 ∨ y = 0
    have aux2 : IsDomain (ZMod p) := by 
      refine ZMod.instIsDomain p
    have aux : NoZeroDivisors (ZMod p) := by 
      exact CancelMonoidWithZero.to_noZeroDivisors
    have eq_or : x - a * y0 = 0 ∨ x + a * y0 = 0 := by 
      refine mul_eq_zero.mp eq2
    obtain eq_or | eq_or := eq_or
    · left
      calc 
        _ = x - a * y0 + a * y0 := by 
          ring_nf
        _ = _ := by 
          rw [eq_or]
          simp
    · right
      calc 
        _ = x + a * y0 - a * y0 := by 
          ring_nf
        _ = _ := by 
          rw [eq_or]
          simp
  · intro h
    obtain h | h := h
    · simp [h, mul_pow, hy0]
    · simp [h, mul_pow, hy0]