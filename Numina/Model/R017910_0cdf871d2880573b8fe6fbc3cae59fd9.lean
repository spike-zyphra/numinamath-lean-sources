import Mathlib

theorem number_theory_101300 (a b c : ℕ) (ha : 0 < a) (hb : a < b) (hc : b < c)
    (hsum : a + b + c = 63) (hq : (b + c) / a = 2) (hrem : (b + c) % a = 15)
    (hdigits : ∃ d, a = d * 10 + d ∨ b = d * 10 + d ∨ c = d * 10 + d) :
    a = 16 ∧ b = 22 ∧ c = 25 := by
  have h1 : b + c = 2 * a + 15 := by 
    rw [←Nat.div_add_mod (b + c) a]
    rw [hq, hrem]
    all_goals omega 
  have h2 : 3 * a = 48 := by 
    omega 
  have ha16 : a = 16 := by 
    omega 
  have hbc47 : b + c = 47 := by 
    rw [ha16] at h1 
    omega 
  rcases hdigits with ⟨d, had⟩ 
  rcases had with (h | h | h)
  · -- Assume a = 11 * d
    exfalso
    have h2 : a = 11 * d := by 
      omega 
    rw [show a = 16 by linarith [ha16]] at h2 
    omega 
  · -- Assume b = 11 * d
    -- Let's suppose b = 11 * d 
    have h2 : b = 11 * d := by 
      omega 
    rw [h2] at hbc47 
    have h3 : c = 47 - 11 * d := by 
      omega 
    -- Now we need to check possible values of k
    -- We need 16 < 11 * d < c
    -- Let's try omega here
  
    have h4 : d = 2 := by
      omega 
    rw [h4] at h2 h3 
    have hb22 : b = 22 := by
      linarith 
    have hc25 : c = 25 := by
      omega 
    exact ⟨ha16, hb22, hc25⟩ 
  · -- Assume c = 11 * d 
    -- Let's suppose c = 11 * d
    exfalso
    have h2 : c = 11 * d := by 
      omega 
    rw [h2] at hbc47 
    have h3 : b = 47 - 11 * d := by 
      omega 
    -- We need 16 < b < c
    rw [h3] at hc 
    rw [h2] at hc 
    -- so, 47 - 11 * d < 11 * d 
    -- that is, 47 < 22 * d
    -- Also b  > 16
    -- so 47 - 11 * d > 16
    -- That is, 31 > 11 * d
    -- So, 3 < d < 31/11
    -- so k is 3
    -- but contradiction
    omega