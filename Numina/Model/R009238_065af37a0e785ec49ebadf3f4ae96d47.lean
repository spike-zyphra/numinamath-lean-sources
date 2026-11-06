import Mathlib

theorem number_theory_4873
    (m n : ℕ)
    (hm : 0 < m)
    (hn : 0 < n)
    (hdiv : m ∣ n) :
    Nat.totient m ∣ Nat.totient n := by 
  exact Nat.totient_dvd_of_dvd hdiv