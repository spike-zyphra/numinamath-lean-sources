import Mathlib

theorem algebra_231125 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hvertex : a * b + a * d + b * c + d * c = 15) :
    a + b + c + d = 8 := by
  have h1 : (a + c) * (b + d) = 15 := by
    nlinarith
  have h2 : a + c ≤ 15 := by
    by_cases h5 : a + c ≤ 15
    · linarith
    · -- Assume for contradiction that a + c > 15
      push_neg at h5
      have h6 : b + d ≤ 1 := by 
        nlinarith [h1, h5]
      have h8 : b ≥ 1 := by linarith [hb]
      have h9 : d ≥ 1 := by linarith [hd]
      have h10 : b + d ≥ 2 := by linarith [h8, h9]
      linarith
  have h2' : b + d ≤ 15 := by
    by_cases h5 : b + d ≤ 15
    · linarith
    · -- Assume for contradiction that b + d > 15
      push_neg at h5
      have h6 : a + c ≤ 1 := by 
        nlinarith [h1, h5]
      have h7 : a ≥ 1 := by linarith [ha]
      have h8 : c ≥ 1 := by linarith [hc]
      have h9 : a + c ≥ 2 := by linarith [h7, h8]
      linarith
  interval_cases h3 : a + c <;> 
    omega