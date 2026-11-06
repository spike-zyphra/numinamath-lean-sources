import Mathlib

theorem number_theory_12112 (a : ℕ) (ha : a > 0) (h : ∃ k, a + a + 2 + a + 4 + a + 6 + a + 8 = k^2)
    (h' : ∃ m, a + 1 + a + 3 + a + 5 + a + 7 = m^3) :
    a + (a + 1) + (a + 2) + (a + 3) + (a + 4) + (a + 5) + (a + 6) + (a + 7) + (a + 8) ≥ 18000 := by
  rcases h with ⟨k, hk⟩
  rcases h' with ⟨m, hm⟩
  have h1 : 5 * a + 20 = k ^ 2 := by
    nlinarith
  have h2 : 4 * a + 16 = m ^ 3 := by
    nlinarith
  by_contra h3
  push_neg at h3
  have h9 : a < 1996 := by
    omega
  have h10 : k < 100 := by
    nlinarith
  have h11 : m < 20 := by
    have h7 : m ^ 3 < 8000 := by
      nlinarith [show 4 * a + 16 < 8000 by
        omega
      ]
    have h8 : m < 20 := by
      by_contra h9
      push_neg at h9
      have h9 : m ≥ 20 := by omega
      have h10 : m ^ 3 ≥ 8000 := by
        have h11 : m ≥ 20 := h9
        have h12 : m ^ 3 ≥ 20 ^ 3 := by
          apply Nat.pow_le_pow_of_le_left h11 3
        norm_num at h12 ⊢
        linarith
      nlinarith
    omega
  interval_cases m <;> try { 
    omega
  } <;> try { 
    have : k < 100 := by nlinarith
    interval_cases k <;> omega
  }