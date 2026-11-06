import Mathlib

/- Show that if \( m \) and \( n \) are positive integers with \( m \mid n \) (meaning \( m \) divides \( n \)), then \( \phi(m) \mid \phi(n) \) (meaning the Euler's totient function of \( m \) divides the Euler's totient function of \( n \)).-/
theorem number_theory_4873
    (m n : ℕ)
    (hm : 0 < m)
    (hn : 0 < n)
    (hdiv : m ∣ n) :
    Nat.totient m ∣ Nat.totient n :=
  -- exact `Nat.totient_dvd_of_dvd` in Mathlib
  Nat.totient_dvd_of_dvd hdiv
