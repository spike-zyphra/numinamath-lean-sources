import Mathlib

theorem number_theory_218267 (x y : ℕ) : 2^(3*x)+5^(3*y)=189 ↔ (x=2 ∧ y=1) := by
  constructor
  · -- Assume 2^(3*x)+5^(3*y)=189, then (x,y) = (2,1)
    intro h
    have h1 : y ≤ 1 := by
      by_contra h2
      push_neg at h2
      have h3 : 3 * y ≥ 6 := by omega
      have h4 : 5 ^ (3 * y) ≥ 5 ^ 6 := by
        apply Nat.pow_le_pow_of_le_right (by norm_num) h3
      have h5 : 5 ^ (3 * y) ≥ 15625 := by
        have h6 : 5 ^ 6 = 15625 := by norm_num
        have h7 : 5 ^ (3 * y) ≥ 5 ^ 6 := h4
        linarith [h6]
      have h8 : 2 ^ (3 * x) > 0 := by
        positivity
      linarith
    have h2 : y = 0 ∨ y = 1 := by omega
    rcases h2 with (hy | hy)
    · -- Case y = 0
      have h3 : 2 ^ (3 * x) = 188 := by
        rw [hy] at h
        norm_num at h ⊢
        linarith
      have h4 : (3 * x) < 8 := by
        by_contra h7
        push_neg at h7
        have h8 : 2 ^ (3 * x) ≥ 2 ^ 8 := by
          apply Nat.pow_le_pow_of_le_right (by norm_num) h7
        have h9 : 2 ^ 8 = 256 := by norm_num
        have h10 : 2 ^ (3 * x) ≥ 256 := by linarith [h9, h8]
        linarith
      interval_cases (3 * x) <;> norm_num at h3 <;> omega
    · -- Case y = 1
      have h3 : 2 ^ (3 * x) = 64 := by
        rw [hy] at h
        norm_num at h ⊢
        linarith
      have h8 : 3 * x = 6 := by
        exact Nat.pow_right_injective (by norm_num) h3
      have hx : x = 2 := by
        omega
      exact ⟨hx, hy⟩
  · -- Assume (x,y) = (2,1), then 2^(3*x)+5^(3*y)=189
    rintro ⟨rfl, rfl⟩
    norm_num