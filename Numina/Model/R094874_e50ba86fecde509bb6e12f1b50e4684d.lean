import Mathlib

/- If a and b are both prime numbers, and $a^{10} + b = 1027$, then $10a + 3b =$ ___          ___. -/
theorem number_theory_8103 (a b : ℕ) (ha : Nat.Prime a) (hb : Nat.Prime b)
    (h : a^10 + b = 1027) : 10 * a + 3 * b = 29 := by 
  have h1 : a ≤ 2 := by
    by_contra h1
    push_neg at h1
    have h2 : a ≥ 3 := by linarith
    have h3 : a^10 > 1027 := by
      have h4 : a ≥ 3 := h2
      have h5 : a^10 ≥ 3^10 := by 
        apply Nat.pow_le_pow_of_le_left
        all_goals linarith
      have h6 : 3^10 > 1027 := by norm_num
      linarith
    have h6 : a^10 + b > 1027 := by 
      omega
    linarith 
  have h2 : a = 2 := by
    interval_cases a <;> norm_num at ha <;> try { contradiction } <;> try { linarith }
  have h3 : b = 3 := by 
    rw [h2] at h
    have h4 : 2^10 + b = 1027 := h
    have h5 : b = 3 := by
      omega
    exact h5
  -- Now compute 10*a + 3*b
  calc
    10 * a + 3 * b = 10 * 2 + 3 * 3 := by rw [h2, h3]
    _ = 20 + 9 := by norm_num
    _ = 29 := by norm_num