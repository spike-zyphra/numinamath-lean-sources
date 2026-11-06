import Mathlib

/- Ancient Chinese Mathematical Problem
Emperor Taizong of Tang ordered the counting of soldiers: if 1,001 soldiers form one camp, then one person is left over; if 1,002 soldiers form one camp, then four people are left over. This time, the counting of soldiers has at least ___ ___. -/
theorem number_theory_1310 {n : ℕ} (hn : n % 1001 = 1 ∧ n % 1002 = 4) :
    n ≥ 1000000 := by
  rcases hn with ⟨h1, h2⟩
  by_contra h
  push_neg at h
  have h3 : n < 1000000 := h
  omega