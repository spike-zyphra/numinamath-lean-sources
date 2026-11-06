import Mathlib

def E (a b c : ℕ) := a * b ^ c

theorem algebra_13030 {r : ℕ} (hr : E r r 3 = 625) :
    r = 5 := by 
  unfold E at hr 
  have h1 : r ^ 4 = 625 := by 
    nlinarith [sq_nonneg (r ^ 2 : ℕ), sq_nonneg (r : ℕ), sq_nonneg (625 - r ^ 4 : ℕ), sq_nonneg (r ^ 2 - r), sq_nonneg (r - 5)]
  have h2 : r ≤ 5 := by 
    by_contra h
    push_neg at h 
    -- h states r > 5
    have h3 : r ≥ 6 := by omega 
    have h4 : r ^ 4 ≥ 6 ^ 4 := by 
      apply Nat.pow_le_pow_of_le_left 
      linarith 
      all_goals linarith 
    norm_num at h4 
    linarith 
  interval_cases r <;> try { 
    omega 
  }