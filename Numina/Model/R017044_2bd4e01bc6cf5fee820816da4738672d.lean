import Mathlib

theorem algebra_148488 (ω : ℂ) (h : ω ^ 3 = 1) (h2 : ω ≠ 1) :
    (1 - ω) * (1 - ω ^ 2) * (1 - ω ^ 4) * (1 - ω ^ 8) = 9 := by
  have h1 : ω ^ 3 = 1 := h
  have hω4 : ω ^ 4 = ω := by
    calc 
      ω ^ 4 = ω ^ 3 * ω := by ring_nf 
      _ = 1 * ω := by rw [h] 
      _ = ω := by ring_nf
  have hω8 : ω ^ 8 = ω ^ 2 := by
    calc 
      ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 := by  ring_nf 
      _ = 1 ^ 2 * ω ^ 2 := by rw [h] 
      _ = ω ^ 2 := by ring_nf
  have h_eq : ω ^ 2 + ω + 1 = 0 := by 
    have h_eq : ω ^ 3 - 1 = 0 := by 
      rw [h]
      all_goals simp [Complex.ext_iff]
    have h_eq2 : ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := by 
      ring_nf 
    rw [h_eq2] at h_eq 
    cases' (mul_eq_zero.1 h_eq) with h_eq3 h_eq4 
    · -- Case where ω - 1 = 0 
      exfalso 
      apply h2 
      have h_eq5 : ω = 1 := by 
        have h_eq6 : ω - 1 = 0 := h_eq3 
        exact eq_of_sub_eq_zero h_eq6 
      exact h_eq5 
    · -- Case where ω ^ 2 + ω + 1 = 0 
      simpa using h_eq4 
  have hω : (1 - ω) * (1 - ω ^ 2) = 3 := by 
    calc 
      (1 - ω) * (1 - ω ^ 2) = 1 - ω - ω ^ 2 + ω ^ 3 := by ring_nf
      _ = 1 - ω - ω ^ 2 + 1 := by rw [h] 
      _ = 2 - (ω + ω ^ 2) := by ring_nf 
      _ = 2 - (-1) := by
        have h_eq_ : ω + ω ^ 2 = -1 := by 
          have eq1 : ω ^ 2 + ω + 1 = 0 := h_eq 
          have : ω + ω ^ 2 = -1 := by 
            calc 
              ω + ω ^ 2 = (ω ^ 2 + ω + 1) - 1 := by ring_nf 
              _ = 0 - 1 := by rw [eq1] 
              _ = -1 := by ring_nf 
          exact_mod_cast this
        rw [h_eq_]
      _ = 3 := by ring_nf
  calc 
    (1 - ω) * (1 - ω ^ 2) * (1 - ω ^ 4) * (1 - ω ^ 8) 
      = (1 - ω) * (1 - ω ^ 2) * (1 - ω) * (1 - ω ^ 2) := by 
        rw [hω4, hω8] 
    _ = ((1 - ω) * (1 - ω ^ 2)) ^ 2 := by ring_nf
    _ = (3) ^ 2 := by rw [hω] 
    _ = 9 := by ring_nf