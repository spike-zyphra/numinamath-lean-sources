import Mathlib

/-- Show that if $\( a, b, c, \)$ and $\( m \)$ are integers such that $\( m > 0 \)$, $\( (c, m) = 1 \)$ (meaning $\( c \)$ and $\( m \)$ are coprime), and if $\( a c \equiv b c \mod m \)$ (which means $\( a c \)$ and $\( b c \)$ leave the same remainder when divided by $\( m \)$), then it follows that $\( a \equiv b \mod m \)$ (which means $\( a \)$ and $\( b \)$ leave the same remainder when divided by $\( m \)$).-/
theorem number_theory_4642 (a b c m : ℤ) (h1 : m > 0)
  (h2 : c.gcd m = 1) :
  (a * c ≡ b * c [ZMOD m]) → (a ≡ b [ZMOD m]) := by
    intro h
    have h3 := Int.ModEq.dvd h
    -- $ac \equiv bc \pmod{m}$ means that $m \mid (b-a) *c$.  
    replace h3 : m ∣ (b - a) * c := by rwa [sub_mul]
    -- Because $(m,c) = 1$, we get $m \mid (b-a)$
    have h4 : m ∣ b - a := IsCoprime.dvd_of_dvd_mul_right (
      IsCoprime.symm ((Int.isCoprime_iff_gcd_eq_one.mpr) h2)) h3
    -- $m \mid (b-a)$ implies that $a \equiv b \pmod {m}$.
    exact Int.modEq_of_dvd  h4