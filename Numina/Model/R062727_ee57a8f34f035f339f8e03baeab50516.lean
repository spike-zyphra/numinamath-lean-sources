import Mathlib

theorem number_theory_233069 (a b : ℕ) (ha : a^3 = 1728) (hb : b^3 = 6859) :
    a = 12 ∧ b = 19 := by
  -- First prove that a = 12.
  have ha1 : a ≤ 12 := by
    by_contra h
    push_neg at h
    -- Assume that a > 12, then a ≥ 13, so a^3 ≥ 13^3 > 1728
    have h1 : a ≥ 13 := by linarith
    have h2 : a^3 ≥ 13^3 := by
      apply Nat.pow_le_pow_of_le_left h1 3
    norm_num at h2
    linarith
  -- Now prove that a ≥ 12
  have ha2 : a ≥ 12 := by
    by_contra h
    push_neg at h
    -- Assume that a < 12, so a ≤ 11, so a^3 ≤ 11^3 < 1728
    have h1 : a ≤ 11 := by linarith
    have h2 : a^3 ≤ 11^3 := by
      apply Nat.pow_le_pow_of_le_left h1 3
    norm_num at h2
    linarith
  -- Hence a = 12
  have ha' : a = 12 := by linarith
  -- Now prove that b = 19
  have hb1 : b ≤ 19 := by
    by_contra h
    push_neg at h
    -- Assume that b > 19, so b ≥ 20, so b^3 ≥ 20^3 > 6859
    have h1 : b ≥ 20 := by linarith
    have h2 : b^3 ≥ 20^3 := by
      apply Nat.pow_le_pow_of_le_left h1 3
    norm_num at h2
    linarith
  -- Now prove that b ≥ 19
  have hb2 : b ≥ 19 := by
    by_contra h
    push_neg at h
    -- Assume that b < 19, so b ≤ 18, so b^3 ≤ 18^3 < 6859
    have h1 : b ≤ 18 := by linarith
    have h2 : b^3 ≤ 18^3 := by
      apply Nat.pow_le_pow_of_le_left h1 3
    norm_num at h2
    linarith
  -- Hence b = 19
  have hb' : b = 19 := by linarith
  -- Therefore, a = 12 and b = 19
  exact ⟨ha', hb'⟩