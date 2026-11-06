import Mathlib

theorem number_theory_44767 (a b c d e f : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hf : f ≠ 0) (h1 : ∃ m, m^2 = 100 * a + 10 * b + c)
    (h2 : ∃ n, n^2 = 100 * d + 10 * e + f) (h3 : ∃ p, p^2 = 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f) :
    ∃ x y z w u v : ℕ, x^2 + y^2 + z^2 = 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f ∧
    w^2 + u^2 + v^2 = 100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f ∧
    (x ≠ w ∨ y ≠ u ∨ z ≠ v) := by
  rcases h3 with ⟨p, hp⟩
  rcases h1 with ⟨m, hm⟩
  rcases h2 with ⟨n, hn⟩
  use 30 * m, 10 * m, n, 10 * m, 30 * m, n
  constructor
  · -- Show that (30 * m) ^ 2 + (10 * m) ^ 2 + n ^ 2 = p^2
    have h4 : p^2 = 1000 * m^2 + n^2 := by
      nlinarith [hp, hm, hn]
    nlinarith [h4]
  constructor
  · -- Show that (10 * m) ^ 2 + (30 * m) ^ 2 + n ^ 2 = p^2
    have h4 : p^2 = 1000 * m^2 + n^2 := by
      nlinarith [hp, hm, hn]
    nlinarith [h4]
  · -- Show the different representations
    have h5 : m > 0 := by
      by_contra h
      have h8 : m = 0 := by
        omega
      rw [h8] at hm
      have h9 : 100 * a + 10 * b + c = 0 := by
        nlinarith
      have h10 : a > 0 := by
        omega
      nlinarith
    have hneq : 30 * m ≠ 10 * m := by
      omega
    left
    exact hneq