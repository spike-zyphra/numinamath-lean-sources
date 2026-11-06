import Mathlib

theorem number_theory_4989 (m u : ℕ) (hu : u ≠ 0) (hm : 1 < m) (r : ZMod m) (h : orderOf r = m.totient)
  : orderOf (r ^ u)  = m.totient ↔ u.Coprime m.totient := by 
    constructor  <;> intro h1
    · -- $ord_m r^u = \frac {\phi(m)} {(u, \phi(m))}$
      have h2 := orderOf_pow' r hu
      simp [h, h1] at h2
      -- prove that $(u, \phi(m) ) = 1$, meaning that $u$ and $\phi(m)$ are coprime.
      have h3 : m.totient.gcd u = 1 :=
        (or_iff_right (Nat.ne_zero_iff_zero_lt.mpr (Nat.totient_pos.mpr (by linarith)))).1 (Nat.div_eq_self.1  h2.symm)
      exact Nat.coprime_comm.mp h3
    · -- $ord_m r^u = \frac {\phi(m)} {(u, \phi(m))}$
      have h2 := orderOf_pow' r hu
      -- Rewrite the fact that $\gcd(u, \phi(m)) = 1$ into the context
      simp [h, h1] at h2 ⊢
      -- Now, the goal is to rewrite $t = t$ 
      have h3 : m.totient.gcd u = 1 := by 
        exact Nat.coprime_comm.mp h1
      rw [h2]
      field_simp [h3]