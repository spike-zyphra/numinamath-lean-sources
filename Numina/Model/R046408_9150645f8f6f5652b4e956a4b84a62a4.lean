import Mathlib

theorem number_theory_15384 (n : ℕ) (h : n = 400) :
    IsLeast {k | ∃ s : Finset ℕ, s.card ≥ 2 ∧ ∑ i ∈ s, (2 : ℕ)^i = n ∧ k = ∑ i ∈ s, i} 19 := by
  rw [h]
  constructor
  · -- First, we show that 19 is in the set.
    use {4, 7, 8}
    native_decide
  · -- Now, we need to prove it is minimality
    intro k hk
    rcases hk with ⟨s, hs1, hsum, hk⟩
    by_contra h'
    push_neg at h'
    have h1 : k < 19 := by omega
    have h8 : ∑ i in s, i < 19 := by
      linarith [hk, h1]
    have h9 : s.card ≥ 2 := hs1
    have h10 : s ⊆ Finset.Icc 0 18 := by
      intro i hi
      have h11 : i ∈ s := hi
      have h12 : ∑ j in s, j < 19 := by
        linarith [h8]
      have h13 : i ≤ 18 := by
        have h14 : i ∈ s := h11
        have h15 : i ≤ ∑ j in s, j := by
          apply Finset.single_le_sum (fun x hx => by simp) h14
        omega
      simp [Finset.mem_Icc]
      omega
    have h5 : ∑ i in s, (2 : ℕ)^i = 400 := hsum
    have h6 : ∑ i in s, i < 19 := h8
    have h7 : s.card ≥ 2 := hs1
    have h8' : s ∈ (Finset.powerset (Finset.Icc 0 18)).filter (fun s => ∑ i in s, (2 : ℕ)^i = 400 ∧ s.card ≥ 2 ∧ (∑ i in s, i < 19)) := by
      have h12 : s ⊆ Finset.Icc 0 18 := h10
      have h14 : s ∈ Finset.powerset (Finset.Icc 0 18) := by 
        exact Finset.mem_powerset.mpr h12
      simp [h14, h5, h7, h6]
    -- Now we prove that the filtered powerset is empty
    have h9' : (Finset.powerset (Finset.Icc 0 18)).filter (fun s => ∑ i in s, (2 : ℕ)^i = 400 ∧ s.card ≥ 2 ∧ (∑ i in s, i < 19)) = ∅ := by 
      native_decide
    rw [h9'] at h8'
    simp at h8'
    all_goals omega