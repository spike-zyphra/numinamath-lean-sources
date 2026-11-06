import Mathlib

theorem number_theory_226889 (M : Finset ℕ) (hM : M = Finset.Icc 1 2017)
    (x : ℕ) (hx : x ∈ M) (hsum : ∃ k, k^2 = ∑ i ∈ M \ {x}, i) :
    x = 1677 := by
  rw [hM] at hx
  rw [hM] at hsum
  rcases hsum with ⟨k, hk⟩
  have h1 : x ≤ 2017 := by
    simp [Finset.mem_Icc] at hx ⊢
    all_goals omega
  have h2 : x ≥ 1 := by 
    simp [Finset.mem_Icc] at hx ⊢
    all_goals omega
  have h42 : k^2 + (x : ℕ) = 2035153 := by 
    have h5 : (∑ i ∈ (Finset.Icc 1 2017) \ {x}, i) + x = 2035153 := by
      have h6 : x ∈ (Finset.Icc 1 2017) := by
        simp [Finset.mem_Icc] at hx ⊢
        all_goals omega
      have h7 : {x} ⊆ (Finset.Icc 1 2017) := by
        intro y hy 
        simp at hy 
        rw [hy] 
        all_goals
          try { tauto }
          try { omega }
      have h8 : (∑ i ∈ (Finset.Icc 1 2017) \ {x}, i) + (∑ i in {x}, i) = (∑ i in (Finset.Icc 1 2017), i) := by
        rw [← Finset.sum_sdiff h7]
        <;> try { 
          simp 
          <;> try { nlinarith } 
        }
      have h9 : (∑ i in {x}, i) = x := by 
        simp 
      have h10 : (∑ i in (Finset.Icc 1 2017), i) = 2035153 := by 
        native_decide 
      linarith [h8, h9, h10]
    omega 
  have h11 : k ≤ 1427 := by 
    by_contra h 
    push_neg at h 
    have h12 : k ^ 2 ≥ 1428 ^ 2 := by
      nlinarith 
    nlinarith [show x ≥ 1 by omega, show x ≤ 2017 by omega]
  have h12 : k ≥ 1426 := by 
    by_contra h 
    push_neg at h 
    have h13 : k ≤ 1425 := by
      omega 
    -- k <= 1425
    have h14 : k ^ 2 ≤ 1425 ^ 2 := by 
      nlinarith [h13, show k ≤ 1425 by linarith, show k ≥ 0 by omega ] 
    nlinarith [show x ≥ 1 by omega, show x ≤ 2017 by omega]
  have h13 : k = 1426 ∨ k = 1427 := by 
    omega 
  rcases h13 with (hk1 | hk2)
  · -- k = 1426
    have hk6 : k = 1426 := hk1
    -- Then k^2 = 2033476.
    -- From h42: k^2 + x = 2035153.
    -- So x = 2035153 - 2033476 = 1677.
    have hx1677 : x = 1677 := by 
      rw [show k = 1426 by linarith [hk6]] at h42
      omega 
    linarith [hx1677]
  · -- k = 1427
    -- This case is impossible.
    have hk7 : k = 1427 := hk2
    -- Then k^2 = 2036329.
    -- From h42: k^2 + x = 2035153.
    -- This gives x = -1176 which is invalid for a natural number x (contradicts x ≥ 1).
    -- Lean should see the contradiction automatically.
    rw [show k = 1427 by linarith [hk7]] at h42 
    omega