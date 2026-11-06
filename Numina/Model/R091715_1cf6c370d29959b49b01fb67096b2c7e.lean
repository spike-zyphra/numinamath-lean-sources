import Mathlib

theorem algebra_73628 :
    ∑ᶠ x ∈ {(a^2 + b^2 + c^2) | (a : ℤ) (b : ℤ) (c : ℤ) (_ : a + b - c = 1) (_ : a^2 + b^2 - c^2 = -1)}, x = 18 := by
  have h1 : {(a^2 + b^2 + c^2) | (a : ℤ) (b : ℤ) (c : ℤ) (_ : a + b - c = 1) (_ : a^2 + b^2 - c^2 = -1)} = {1, 17} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · 
      rintro ⟨a, b, c, h1, h2, rfl⟩
      have h3 : c = a + b - 1 := by linarith
      rw [h3] at h2
      have h4 : (a - 1) * (b - 1) = 1 := by
        nlinarith 
      have h5 : (a - 1) = 1 ∨ (a - 1) = -1 := by 
        apply Int.eq_one_or_neg_one_of_mul_eq_one 
        exact h4
      cases h5 with
      | inl ha1 =>
        have ha : a = 2 := by linarith
        have hb : b = 2 := by 
          have : b - 1 = 1 := by 
            rw [ha1] at h4
            linarith 
          linarith
        have hc : c = 3 := by 
          rw [ha, hb] at h3
          linarith 
        norm_num [ha, hb, hc]
        all_goals omega
      | inr ha1 =>
        have ha : a = 0 := by linarith
        have hb : b = 0 := by 
          have : b - 1 = -1 := by 
            rw [ha1] at h4
            linarith 
          linarith
        have hc : c = -1 := by 
          rw [ha, hb] at h3
          linarith 
        norm_num [ha, hb, hc]
        all_goals omega
    · 
      rintro (rfl | rfl)
      · 
        use 0, 0, -1
        all_goals norm_num
      · 
        use 2, 2, 3
        all_goals norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num
  <;> try { linarith }
  <;> try { native_decide }