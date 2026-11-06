import Mathlib

theorem number_theory_172736 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 2 * a + 1 ∣ 3 * b - 1) (h2 : 2 * b + 1 ∣ 3 * a - 1) :
    (a, b) = (2, 2) ∨ (a, b) = (12, 17) ∨ (a, b) = (17, 12) := by
  rcases h1 with ⟨k, hk1⟩
  rcases h2 with ⟨m, hk2⟩

  have eq1 : 3 * b = 2 * a * k + k + 1 := by 
    nlinarith

  have eq2 : 3 * a = 2 * b * m + m + 1 := by
    nlinarith

  have h4 : k > 0 := by
    nlinarith [show 0 < 2 * a + 1 by nlinarith, show 0 < b by linarith]

  have h5 : m > 0 := by
    nlinarith [show 0 < 2 * b + 1 by nlinarith, show 0 < a by linarith]

  have h6 : k * m ≤ 9 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (k - m), sq_pos_of_pos (show 0 < a by linarith), 
              sq_pos_of_pos (show 0 < b by linarith), mul_pos ha hb, 
              mul_pos ha (show 0 < 2 * b + 1 by nlinarith), 
              mul_pos (show 0 < 2 * a + 1 by nlinarith) hb
            ]

  have hk8 : k ≤ 9 := by 
    have h6' : k * m ≤ 9 := h6 
    have hm1 : m ≥ 1 := by nlinarith
    nlinarith

  have hm9 : m ≤ 9 := by 
    have h6' : k * m ≤ 9 := h6 
    have hk1 : k ≥ 1 := by nlinarith
    nlinarith

  interval_cases k <;> try { 
    omega 
  } <;> try { 
      interval_cases m 
      <;> norm_num [Prod.ext_iff] at *
      <;> omega 
  }