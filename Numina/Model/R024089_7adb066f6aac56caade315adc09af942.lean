import Mathlib

theorem algebra_98413 : {(m, n) : ℤ × ℤ | m + n = m * n}.encard = 2 := by
  have h1 : {(m, n) : ℤ × ℤ | m + n = m * n} = {(2, 2), (0, 0)} := by
    ext ⟨m, n⟩
    simp 
    constructor
    · -- If (m, n) is in the set, then m + n = m * n
      rintro H
      have h2 : m + n = m * n := H
      have h3 : (m - 1) * (n - 1) = 1 := by
        linarith 
      have h4 : (m - 1) * (n - 1) = 1 := h3
      have h5 : (m - 1) = 1 ∨ (m - 1) = -1 := by
        apply Int.eq_one_or_neg_one_of_mul_eq_one 
        exact h4
      cases h5 with
      | inl h6 =>
        -- m - 1 = 1, so m = 2 
        have h7 : n - 1 = 1 := by 
          rw [h6] at h4 
          linarith 
        have hm : m = 2 := by linarith 
        have hn : n = 2 := by linarith 
        left 
        simp [hm, hn]
      | inr h8 =>
        -- m - 1 = -1, so m = 0 
        have h7 : n - 1 = -1 := by 
          rw [h8] at h4 
          linarith 
        have hm : m = 0 := by linarith 
        have hn : n = 0 := by linarith 
        right 
        simp [hm, hn]
    · -- Backward direction. If (m, n) is in the right side, then m + n = m * n
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (2, 2)
        norm_num 
      · -- Check (0, 0)
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  <;> try { all_goals tauto }