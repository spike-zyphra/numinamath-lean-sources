import Mathlib

theorem number_theory_286404 (n : ℕ) (h₀ : n^3 ∈ Finset.Icc 10000 99999) (h₁ : (n^3)/10000=4) (h₂ : (n^3)%10=6) :
    n=36 := by
  have h3 : 10000 ≤ n^3 := by 
    simp [Finset.mem_Icc] at h₀
    omega 
  have h4 : n^3 ≤ 99999 := by 
    simp [Finset.mem_Icc] at h₀ 
    omega 
  have h7 : n ≥ 35 := by 
    by_contra h 
    push_neg at h 
    have h8 : n ≤ 34 := by omega 
    have h9 : n ^ 3 < 40000 := by 
      have h50 : n ≤ 34 := h8 
      have h51 : n ^ 3 ≤ 34 ^ 3 := by 
        apply Nat.pow_le_pow_of_le_left 
        omega 
      norm_num at h51 ⊢ 
      omega 
    have h9 : n ^ 3 / 10000 < 4 := by 
      rw [Nat.div_lt_iff_lt_mul] 
      all_goals omega 
    omega 
  have h8 : n < 38 := by 
    by_contra h 
    push_neg at h 
    have h2 : n ≥ 38 := by omega 
    have h10 : n ^ 3 ≥ 50000 := by 
      have h20 : n ≥ 38 := h2 
      have h3 : n ^ 3 ≥ 38 ^ 3 := by 
        apply Nat.pow_le_pow_of_le_left 
        omega 
      norm_num at h3 ⊢ 
      omega 
    omega 
  have : n = 35 ∨ n = 36 ∨ n = 37 := by 
    omega 
  rcases this with (h | h | h) 
  · -- n = 35
    rw [show n = 35 by omega] at h₂ 
    norm_num at h₂ 
  · -- n = 36 
    omega 
  · -- n = 37 
    rw [show n = 37 by omega] at h₂ 
    norm_num at h₂