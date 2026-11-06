import Mathlib
/-- Show that if $\(a\)$, $\(b\)$, $\(c\)$, and $\(m\)$ are integers such that $\(m > 0\)$, $\(d = (c, m)\)$, and $\(a c \equiv b c \pmod{m}\)$, then it follows that $\(a \equiv b \pmod{m / d}\)$.-/
theorem number_theory_4641
(a b c m : ℤ)
(mpos : m > 0)
(h : c * a ≡ c * b [ZMOD m]) :
a ≡ b [ZMOD (m / Int.gcd c m)] := by
  have := Int.ModEq.dvd h
  -- $ac = bc \pmod{m}$ implies $m \mid c(b-a)$. 
  have h1 : m ∣ c * (b - a) := by rwa [mul_sub]
  -- according to the above equation, we get $m/(c,m) \mid (b - a)$. 
  have h2 : m / c.gcd m ∣ (b - a) := by
    have : m / c.gcd m ∣ c * (b - a) / c.gcd m := Int.ediv_dvd_ediv (Int.gcd_dvd_right) h1
    have : m / c.gcd m ∣ c / c.gcd m * (b - a) := by
      rw [mul_comm, Int.mul_ediv_assoc, mul_comm] at this
      exact this
      exact Int.gcd_dvd_left
    refine IsCoprime.dvd_of_dvd_mul_left (by
      refine Int.isCoprime_iff_gcd_eq_one.mpr ?_
      rw [Int.gcd_comm c m]
      refine Int.gcd_div_gcd_div_gcd (Int.gcd_pos_of_ne_zero_left c (by linarith))
      ) this
  exact Int.modEq_of_dvd h2
