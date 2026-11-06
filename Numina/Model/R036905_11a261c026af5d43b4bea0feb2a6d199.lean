import Mathlib

theorem number_theory_6047 (n : ℕ) (h : n > 0) (h1 : Odd n) (h2 : 596 = (n^2) + ((n+2)^2) + ((n+4)^2) + ((n+6)^2)) :
    n = 9 := by
  have h3 : n ≤ 17 := by
    nlinarith [h2]
  interval_cases n <;> norm_num at h2 <;> try { tauto }
  <;> try { contradiction }