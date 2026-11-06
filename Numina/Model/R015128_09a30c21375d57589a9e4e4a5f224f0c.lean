import Mathlib

theorem number_theory_251414 {n : ℕ} (hn : n > 0) :
    (10 * n + 1) % 1000000 = n * 3 ↔ n = 142857 := by 
  constructor
  · -- Assume (10 * n + 1) % 1000000 = n * 3, prove n = 142857
    intro h
    have h1 : (10 * n + 1) % 1000000 = n * 3 := h
    have h2 : n = 142857 := by
      omega
    exact_mod_cast h2
  · -- Assume n = 142857, prove the congruence
    intro h 
    subst h
    norm_num