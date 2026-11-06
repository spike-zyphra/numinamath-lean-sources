import Mathlib

theorem number_theory_7897 (n : ℕ) (h : IsGreatest {n : ℕ | (n ∈ Finset.Icc 100 999) ∧
    Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 6 ∣ n} n) :
    (Nat.digits 10 n).sum = 24 := by
  have h11 : n ∈ Finset.Icc 100 999 := by
    have h11 := h.left
    simp at h11 ⊢
    tauto
  -- From h11, we can derive the bounds
  have h12 : n ≥ 100 := by 
    simp [Finset.mem_Icc] at h11
    omega
  have h13 : n ≤ 999 := by 
    simp [Finset.mem_Icc] at h11
    omega

  -- From h, we can derive the divisibility and palindrome conditions
  have h14 : 6 ∣ n := by 
    have h11 := h.left
    simp at h11 ⊢
    tauto

  have h15 : Nat.digits 10 n = List.reverse (Nat.digits 10 n) := by
    have h11 := h.left
    simp at h11 ⊢
    tauto
  
  -- Also, any m in the set must be ≤ n.
  have h6 : ∀ m, (m ∈ Finset.Icc 100 999 ∧ Nat.digits 10 m = List.reverse (Nat.digits 10 m) ∧ 6 ∣ m) → m ≤ n := by
    apply h.right
  
  -- Show n ≥ 888 by using h6
  have h8 : n ≥ 888 := by
    have h9 := h6 888 (by
      constructor
      · -- Show 888 ∈ [100, 999]
        simp [Finset.mem_Icc]
      constructor 
      · -- Show Nat.digits 888 = List.reverse (Nat.digits 888)
        native_decide
      · -- Show 6 ∣ 888
        norm_num 
    )
    omega
  
  -- Show that n ≤ 888 by contradiction
  have h7 : n ≤ 888 := by 
    by_contra h8
    push_neg at h8
    have h9 : n > 888 := by omega
    -- Since n ≤ 999, we can consider cases
    have h31 : n ≤ 999 := by 
      simp [Finset.mem_Icc] at h11
      omega
    have h4 : n ≥ 889 := by omega 
    -- Check all cases from 889 to 999, they must satisfy our properties.
    interval_cases n <;> norm_num at h14 h15 h11 ⊢ 
    <;> try { contradiction }
    <;> omega
  
  -- Thus n must be 888
  have h10 : n = 888 := by 
    omega
  
  -- The digits sum: 8 + 8 + 8 = 24
  rw [h10]
  native_decide