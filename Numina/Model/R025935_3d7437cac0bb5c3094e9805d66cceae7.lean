import Mathlib

theorem number_theory_262725 (a b c d : ℕ) (ha : Odd a) (hb : Odd b) (hc : Odd c) (hd : Odd d)
    (h : 2016 ∣ (10000000 + 100000 * a + 20000 + 1000 * b + 100 * c + 10 * d)) :
    10000000 + 100000 * a + 20000 + 1000 * b + 100 * c + 10 * d = 3290313652307136 := by
  rcases ha with ⟨m, hm⟩
  rcases hb with ⟨n, hn⟩
  rcases hc with ⟨p, hp⟩
  rcases hd with ⟨q, hq⟩
  omega