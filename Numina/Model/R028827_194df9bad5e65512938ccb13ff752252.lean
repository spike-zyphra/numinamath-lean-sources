import Mathlib

theorem algebra_154405 (a S : ℤ) (hS : S = ∑ i ∈ Finset.range 7, (a + i * d)) (hd : d > 0)
    (h18 : (a + 7 * d) * (a + 16 * d) > S + 27)
    (h19 : (a + 10 * d) * (a + 13 * d) < S + 60) :
    a = -11 ∨ a = -10 ∨ a = -9 ∨ a = -7 ∨ a = -6 ∨ a = -5 := by
  have h2 : S = 7 * a + 21 * d := by 
    rw [hS]
    simp only [Finset.sum_range_succ]
    ring
  rw [h2] at h18 h19
  have h3 : d ≥ 1 := by 
    omega
  have h4 : a ^ 2 + 23 * a * d + 112 * d ^ 2 - 7 * a - 21 * d - 27 > 0 := by 
    nlinarith 
  have h5 : a ^ 2 + 23 * a * d + 130 * d ^ 2 - 7 * a - 21 * d - 60 < 0 := by 
    nlinarith 
  have h6 : d ≤ 4 := by
    nlinarith [sq_nonneg (a + 10 * d), sq_nonneg (a + 13 * d), sq_nonneg (a + 7 * d), sq_nonneg (a + 16 * d), sq_nonneg (a + 4), sq_nonneg (a + 5), sq_nonneg (a - 1)]
  have h7 : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by 
    omega 
  rcases h7 with (h | h | h | h) <;> 
    simp_all only [h, mul_pos] <;> 
      try { 
        have : (a ≤ 20) ∧ (a ≥ -20) := by
          constructor 
          <;> nlinarith 
        rcases this with ⟨ha1, ha2⟩ 
        interval_cases a <;> omega 
      }