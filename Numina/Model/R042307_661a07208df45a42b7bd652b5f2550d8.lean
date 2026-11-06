import Mathlib

theorem number_theory_8586 (a b c d e f : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) (h1 : ∃ m, m^2 = 100 * a + 10 * b + c)
    (h2 : ∃ n, n^2 = 100 * d + 10 * e + f) (h3 : ∃ p, p^2 = 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f) :
    ∃ q r s t u v : ℕ, q^2 + r^2 + s^2 = 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f ∧
    t^2 + u^2 + v^2 = 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f ∧
    q ≠ t := by

  rcases h3 with ⟨p, hp⟩
  use p, 0, 0, 0, p, 0
  constructor
  · -- Show that q^2 + r^2 + s^2 = ... 
    nlinarith
  constructor
  · -- Show that t^2 + u^2 + v^2 = ... 
    nlinarith
  · -- Show that q ≠ t.
    by_contra h
    have h4 : p = 0 := by
      omega
    rw [h4] at hp
    omega