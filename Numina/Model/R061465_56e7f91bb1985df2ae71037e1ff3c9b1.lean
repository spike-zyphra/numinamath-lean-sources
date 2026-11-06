import Mathlib

theorem number_theory_290659 {a b : ℕ} (ha : IsGreatest {x | 0 < x ∧ x^3 < 999} a)
    (hb : IsLeast {x | 0 < x ∧ x^5 > 99} b) : a - b = 6 := by
  have ha1 : a ∈ {x | 0 < x ∧ x^3 < 999} := ha.left
  have ha2 : ∀ x ∈ {x | 0 < x ∧ x^3 < 999}, x ≤ a := ha.right
  have ha3 : a > 0 := by
    simpa using ha1.left
  have ha4 : a^3 < 999 := by
    simpa using ha1.right
  have ha5 : a ≥ 9 := by
    have h9 : (9 : ℕ) ∈ {x | 0 < x ∧ x^3 < 999} := by
      refine ⟨by norm_num, ?_⟩
      norm_num
    have h9a : 9 ≤ a := ha2 9 h9
    linarith
  have ha6 : a ≤ 9 := by
    by_contra h
    push_neg at h
    have h10 : a ≥ 10 := by 
      omega
    have h3 : a^3 ≥ 1000 := by
      have h_a : a ≥ 10 := h10
      have h_a3 : a^3 ≥ 10^3 := by
        apply Nat.pow_le_pow_of_le_left h_a 3
      norm_num at h_a3
      linarith
    linarith
  have ha7 : a = 9 := by 
    omega 
  have hb1 : b ∈ {x | 0 < x ∧ x^5 > 99} := hb.left
  have hb2 : ∀ x ∈ {x | 0 < x ∧ x^5 > 99}, b ≤ x := hb.right
  have hb3 : b > 0 := by
    simpa using hb1.left
  have hb4 : b^5 > 99 := by 
    simpa using hb1.right
  have hb5 : b ≥ 3 := by 
    by_contra h 
    push_neg at h 
    have h2 : b ≤ 2 := by 
      linarith 
    interval_cases b <;> norm_num at hb4
    all_goals try linarith 
  have hb6 : b ≤ 3 := by
    have h3 : (3 : ℕ) ∈ {x | 0 < x ∧ x^5 > 99} := by 
      refine ⟨by norm_num, ?_⟩
      norm_num 
    have h3b : b ≤ 3 := hb2 3 h3 
    linarith 
  have hb7 : b = 3 := by 
    omega 
  calc 
    a - b = 9 - 3 := by rw [ha7, hb7]
    _ = 6 := by norm_num