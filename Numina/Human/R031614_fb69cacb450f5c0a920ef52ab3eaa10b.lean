import Mathlib

/-- Show that if $\( r \)$ is a primitive root modulo $\( m \)$, where $\( m \)$ is an integer greater than 1, then $\( r^{u} \)$ is also a primitive root modulo $\( m \)$ if and only if the greatest common divisor of $\( u \)$ and $\( \phi(m) \)$ is equal to 1. -/
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
    · simp [orderOf_pow' r hu, h, h1]
      have : m.totient.gcd u = 1 := h1.symm
      simp [this]
