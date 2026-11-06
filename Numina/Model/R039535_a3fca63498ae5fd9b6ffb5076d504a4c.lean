import Mathlib

theorem number_theory_294133 (a : ℕ) (ha : a > 0) (h1 : ∃ n, n^2 = a + a + 2 + a + 4 + a + 6 + a + 8)
    (h2 : ∃ m, m^3 = a + 1 + a + 3 + a + 5 + a + 7) :
    a + (a + 1) + (a + 2) + (a + 3) + (a + 4) + (a + 5) + (a + 6) + (a + 7) + (a + 8) ≥ 18000 := by 
  rcases h1 with ⟨n, hn⟩
  rcases h2 with ⟨m, hm⟩
  have eq1 : a + a + 2 + a + 4 + a + 6 + a + 8 = 5 * a + 20 := by 
    omega
  have eq2 : a + 1 + a + 3 + a + 5 + a + 7 = 4 * a + 16 := by 
    omega
  rw [eq1] at hn
  rw [eq2] at hm
  by_contra h
  push_neg at h
  have h_eq : a + (a + 1) + (a + 2) + (a + 3) + (a + 4) + (a + 5) + (a + 6) + (a + 7) + (a + 8) < 18000 := by 
    omega
  have h6 : n ≤ 99 := by
    nlinarith
  have h7 : m ≤ 19 := by
    by_contra h8
    push_neg at h8
    have h8 : m ≥ 20 := by omega
    have h9 : 4 * a + 16 ≥ 8000 := by
      have : m^3 ≥ 8000 := by
        have h81 : m ≥ 20 := by omega
        have h82 : m^3 ≥ 20^3 := by
          apply Nat.pow_le_pow_left
          all_goals omega
        nlinarith
      omega
    have h10 : a ≥ 1996 := by
      omega
    nlinarith
  interval_cases n <;> try { 
    omega
  } <;> try { 
    interval_cases m <;> omega
  }