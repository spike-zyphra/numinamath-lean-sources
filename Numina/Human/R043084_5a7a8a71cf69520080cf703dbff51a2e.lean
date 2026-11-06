import Mathlib

/-- Show that if $\( r_{1}, r_{2}, \ldots, r_{m} \)$ forms a complete system of residues modulo $\( m \)$, and if $\( a \)$ is a positive integer such that $\( (a, m) = 1 \)$, then the set of integers $\( a r_{1} + b, a r_{2} + b, \ldots, a r_{m} + b \)$ also forms a complete system of residues modulo $\( m \)$.-/
theorem number_theory_4644 (a b m : ℤ) (_ : 0 < a) (h : a.gcd m = 1)
  (hr : a * r1 + b ≡ a * r2 + b [ZMOD m]) : r1 ≡ r2 [ZMOD m] := by
    -- Because $r_1,r_2, \cdots, r_m$ forms a complete system of residues module $m$, we just need to prove that if $r_i \not \equiv r_j \pmod{m}$, then $ar_1 + b \not \equiv ar_2 + b \pmod{m}$.
    -- So we just need prove $ar_1 + b \equiv ar_2 + b \pmod{m}$ implies that $r_i \equiv r_j \pmod{m}$.
    have h1 : a * r1 ≡ a * r2 [ZMOD m] := by exact Int.ModEq.add_right_cancel' b hr
    have h3 := Int.ModEq.dvd h1
    replace h3 : m ∣ a * (r2 - r1):= by rwa [mul_sub]
    have h4 : m ∣ r2 - r1 := IsCoprime.dvd_of_dvd_mul_left (
      IsCoprime.symm ((Int.isCoprime_iff_gcd_eq_one.mpr) h)) h3
    exact Int.modEq_of_dvd  h4
