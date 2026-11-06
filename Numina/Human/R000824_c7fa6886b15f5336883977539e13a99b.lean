import Mathlib

set_option maxHeartbeats 2000000

/-How many of the numbers from the set $\{1,\ 2,\ 3,\ldots,\ 50\}$ have a perfect square factor other than one?-/
theorem algebra_16778 :
    {n : ℕ | n ∈ Finset.Icc 1 50 ∧ ∃ k, k^2 ∣ n ∧ k ≠ 1}.ncard = 19 := by
  set s₂ := {n : ℕ | n ∈ Finset.Icc 1 50 ∧ 2 ^ 2 ∣ n} with hs2
  set s₃ := {n : ℕ | n ∈ Finset.Icc 1 50 ∧ 3 ^ 2 ∣ n} with hs3
  set s₄ := {n : ℕ | n ∈ Finset.Icc 1 50 ∧ 4 ^ 2 ∣ n} with hs4
  set s₅ := {n : ℕ | n ∈ Finset.Icc 1 50 ∧ 5 ^ 2 ∣ n} with hs5
  set s₆ := {n : ℕ | n ∈ Finset.Icc 1 50 ∧ 6 ^ 2 ∣ n} with hs6
  set s₇ := {n : ℕ | n ∈ Finset.Icc 1 50 ∧ 7 ^ 2 ∣ n} with hs7
  -- show that the desired set is equal to unions of sᵢ
  have equiv_set : {n : ℕ | n ∈ Finset.Icc 1 50 ∧ ∃ k, k^2 ∣ n ∧ k ≠ 1} = s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ∪ s₇ := by
    ext n
    simp
    apply Iff.intro <;> intro h
    -- case 1 : ∃ k, k ^ 2 ∣ n
    . obtain ⟨hn, k, hkn, hk⟩ := h
      match k with
      | 0 => -- when k = 0
        norm_num at hkn
        linarith only [hkn, hn]
      | 1 => -- when k = 1
        norm_num at hk
      | 2 => -- when k = 2
        norm_num at hkn
        left; left; left; left; left
        rw [hs2]
        simp
        tauto
      | 3 => -- when k = 3
        norm_num at hkn
        left; left; left; left; right
        rw [hs3]
        simp
        tauto
      | 4 => -- when k = 4
        norm_num at hkn
        left; left; left; right
        rw [hs4]
        simp
        tauto
      | 5 => -- when k = 5
        norm_num at hkn
        left; left; right
        rw [hs5]
        simp
        tauto
      | 6 => -- when k = 6
        norm_num at hkn
        left; right
        rw [hs6]
        simp
        tauto
      | 7 => -- when k = 7
        norm_num at hkn
        right
        rw [hs7]
        simp
        tauto
      | k + 8 => --when k ≥ 8
        ring_nf at hkn
        have ineq₁ : 64 ≤ 64 + k * 16 + k ^ 2 := by linarith only [show 0 ≤ k ^ 2 + 16 * k by positivity]
        have ineq₂ : n < 64 + k * 16 + k ^ 2 := by linarith only [ineq₁, hn]
        apply Nat.eq_zero_of_dvd_of_lt at hkn
        apply hkn at ineq₂
        linarith only [ineq₂, hn]
    -- case 2 : n ∈ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ∪ s₇
    . cases h with
    | inr h => -- when n ∈ s₇
      rw [hs7] at h
      simp at h
      refine ⟨?_, ?_⟩
      . tauto
      . use 7
        norm_num
        tauto
    | inl h => -- when n ∉ s₇
      cases h with
      | inr h => -- when n ∈ s₆
        rw [hs6] at h
        simp at h
        refine ⟨?_, ?_⟩
        . tauto
        . use 6
          norm_num
          tauto
      | inl h => -- when n ∉ s₆ ∪ s₇
        cases h with
        | inr h => -- when n ∈ s₅
          rw [hs5] at h
          simp at h
          refine ⟨?_, ?_⟩
          . tauto
          . use 5
            norm_num
            tauto
        | inl h => -- when n ∉ s₅ ∪ s₆ ∪ s₇
          cases h with
          | inr h => -- when n ∈ s₄
            rw [hs4] at h
            simp at h
            refine ⟨?_, ?_⟩
            . tauto
            . use 4
              norm_num
              tauto
          | inl h => -- when n ∈ s₂ ∪ s₃
            cases h with
            | inr h => -- when n ∈ s₃
              rw [hs3] at h
              simp at h
              refine ⟨?_, ?_⟩
              . tauto
              . use 3
                norm_num
                tauto
            | inl h => -- when n ∈ s₂
              rw [hs2] at h
              simp at h
              refine ⟨?_, ?_⟩
              . tauto
              . use 2
                norm_num
                tauto
  
  -- show the ncard of sᵢ is 50 / (i ^ 2)
  have ncard_s (k : ℕ) (hk : 2 ≤ k) : {n : ℕ | n ∈ Finset.Icc 1 50 ∧ k ^ 2 ∣ n}.ncard = 50 / (k ^ 2) := by
    -- set function φ : n ↦ k ^ 2 * n
    let φ : ℕ → ℕ := fun n ↦ k ^ 2 * n
    -- show that φ is injective at Finset.Icc 1 (50 / k ^ 2)
    have inj_φ : Set.InjOn φ (Finset.Icc 1 (50 / k ^ 2)) := by
      intro n hn m hm φeq
      simp at hn hm
      simp [φ] at φeq
      cases φeq with
      | inr h => -- when k = 0, contradiction!
        linarith only [hk, h]
      | inl h => -- when n = m
        exact h
    -- show that the image of φ is sₖ
    have imφ : φ ''(Finset.Icc 1 (50 / k ^ 2)) = {n : ℕ | n ∈ Finset.Icc 1 50 ∧ k ^ 2 ∣ n} := by
      ext n
      simp [φ]
      -- divide into two parts
      apply Iff.intro <;> intro h
      -- show that k ^ 2 ∣ n and the range of n
      . obtain ⟨x, hx, hn⟩ := h
        rw [<-hn]
        simp
        refine ⟨?_, ?_⟩
        -- show that 1 ≤ k ^ 2 * x
        . nlinarith only [hx, hk]
        . calc
            k ^ 2 * x ≤ k ^ 2 * (50 / k ^ 2) := by apply mul_le_mul; simp; tauto; linarith only [hx]; positivity
            _ ≤ 50 := by apply Nat.mul_div_le
      -- show that 1 ≤ n / k ^ 2 ≤ 50 / k ^ 2
      . obtain ⟨hn, t, ht⟩ := h
        use t
        -- show that t ≤ 50 / k ^ 2
        have _ : t ≤ 50 / k ^ 2 := by
          calc
            t = n / k ^ 2 := by rw [ht]; rw [@Nat.mul_div_right]; positivity
            _ ≤ 50 / k ^ 2 := by apply Nat.div_le_div; tauto; simp; nlinarith only [hk]
        -- show that 1 ≤ t
        have _ : 1 ≤ t := by 
          cases t with
          -- when t = 0, contradiction!
          | zero =>
            norm_num at ht ⊢
            rw [ht] at hn
            norm_num at hn
          -- when t = z + 1
          | succ z =>
            linarith only [show 0 ≤ z by positivity]
        tauto
    
    -- calculate that ncard of sₖ is 50 / k ^ 2
    calc
      {n | n ∈ Finset.Icc 1 50 ∧ k ^ 2 ∣ n}.ncard = (φ ''(Finset.Icc 1 (50 / k ^ 2) : Set ℕ)).ncard := by rw [imφ]
      _ = (Finset.Icc 1 (50 / k ^ 2) : Set ℕ).ncard := by apply Set.ncard_image_of_injOn; exact inj_φ
      _ = (Finset.Icc 1 (50 / k ^ 2)).card := by rw [Set.ncard_coe_Finset]
      _ = 50 / k ^ 2 := by rw [Nat.card_Icc, Nat.add_sub_cancel]  
  
  -- so that we get ncard of each sₖ 
  have ncard_2 : s₂.ncard = 12 := by rw [hs2]; apply ncard_s; norm_num
  have ncard_3 : s₃.ncard = 5 := by rw [hs3]; apply ncard_s; norm_num
  have ncard_5 : s₅.ncard = 2 := by rw [hs5]; apply ncard_s; norm_num
  have ncard_6 : s₆.ncard = 1 := by rw [hs6]; apply ncard_s; norm_num
  have ncard_7 : s₇.ncard = 1 := by rw [hs7]; apply ncard_s; norm_num

  -- show that s₄ ⊆ s₂
  have h2cons4 : s₄ ⊆ s₂ := by 
    rw [hs2, hs4]
    simp
    intro a _ _ da
    obtain ⟨b, hb⟩ := da
    have _ : 4 ∣ a := by
      use (4 * b)
      ring_nf at hb ⊢
      exact hb
    tauto
  -- show that s₆ ⊆ s₂
  have h2cons6 : s₆ ⊆ s₂ := by
    rw [hs2, hs6]
    simp
    intro a _ _ da
    obtain ⟨b, hb⟩ := da
    have _ : 4 ∣ a := by
      use (9 * b)
      ring_nf at hb ⊢
      exact hb
    tauto
  -- show that s₂ ∩ s₃ = s₆
  have inter23 : s₂ ∩ s₃ = s₆ := by
    rw [hs2, hs3, hs6]
    ext n
    simp
    apply Iff.intro <;> intro h
    -- show that 36 ∣ n
    . obtain ⟨⟨_, h4⟩, ⟨_, h9⟩⟩ := h
      have h36 : 4 * 9 ∣ n := by
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        norm_num
        repeat assumption
      norm_num at h36
      tauto
    -- show that 4 ∣ n and 9 ∣ n
    . obtain ⟨hn, m, hm36⟩ := h
      have _ : 4 ∣ n := by use (9 * m); ring_nf at hm36 ⊢; exact hm36
      have _ : 9 ∣ n := by use (4 * m); ring_nf at hm36 ⊢; exact hm36
      tauto
  
  -- so combine the proposition of s₄ and s₆, we have the conclusion is ncard of s₂ ∪ s₃ ∪ s₅ ∪ s₇
  replace equiv_set : {n : ℕ | n ∈ Finset.Icc 1 50 ∧ ∃ k, k^2 ∣ n ∧ k ≠ 1} = s₂ ∪ s₃ ∪ s₅ ∪ s₇ := by
    calc
      {n : ℕ | n ∈ Finset.Icc 1 50 ∧ ∃ k, k^2 ∣ n ∧ k ≠ 1} = s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ∪ s₇ := by rw [equiv_set]
      _ = s₂ ∪ s₃ ∪ s₅ ∪ s₆ ∪ s₇ := by congr 3; apply Set.union_eq_self_of_subset_right; apply Set.subset_union_of_subset_left; exact h2cons4
      _ = s₂ ∪ s₃ ∪ s₅ ∪ s₇ := by congr 1; apply Set.union_eq_self_of_subset_right; apply Set.subset_union_of_subset_left; apply Set.subset_union_of_subset_left; exact h2cons6
  clear h2cons4 h2cons6 ncard_s

  -- show that s₇ is disjoint with s₂ ∪ s₃ ∪ s₅
  have disjoint7 : s₇ ∩ (s₂ ∪ s₃ ∪ s₅) = ∅ := by
    ext n
    simp
    rw [hs2, hs3, hs5, hs7]
    simp
    intro hnl hnr hn49 
    obtain ⟨m, hm⟩ := hn49
    -- actually we discuss the case of m
    match m with
    -- when m = 0, contradiction!
    | 0 => norm_num at hm; rw [hm] at hnl; norm_num at hnl
    -- when m ≥ 2, contradiction!
    | m + 2 => linarith only [hnr, show 98 ≤ n by ring_nf at hm; linarith]
    -- when m = 1, verified
    | 1 => norm_num at hm; rw [hm]; norm_num
  -- show that s₅ is disjoint with s₂ ∪ s₃
  have disjoint5 : s₅ ∩ (s₂ ∪ s₃) = ∅ := by
    ext n
    simp
    rw [hs2, hs3, hs5]
    simp
    intro hnl hnr hn25 
    obtain ⟨m, hm⟩ := hn25
    -- actually we discuss the case of m
    match m with
    -- when m = 0, contradiction!
    | 0 => norm_num at hm; rw [hm] at hnl; norm_num at hnl
    -- when m ≥ 3, contradiction!
    | m + 3 => linarith only [hnr, show 75 ≤ n by ring_nf at hm; linarith]
    -- when m = 1, 2, verified!
    | 1 => rw [hm]; norm_num
    | 2 => rw [hm]; norm_num
  
  -- calculate the conclusion
  calc
    {n : ℕ | n ∈ Finset.Icc 1 50 ∧ ∃ k, k^2 ∣ n ∧ k ≠ 1}.ncard = (s₂ ∪ s₃ ∪ s₅ ∪ s₇).ncard := by rw [equiv_set]
    _ = (s₇ ∪ (s₂ ∪ s₃ ∪ s₅)).ncard + (s₇ ∩ (s₂ ∪ s₃ ∪ s₅)).ncard := by rw [disjoint7]; simp; rw [Set.union_comm]
    -- exactly calculate that (s₇ ∪ (s₂ ∪ s₃ ∪ s₅)).ncard + (s₇ ∩ (s₂ ∪ s₃ ∪ s₅)).ncard = s₇.ncard + (s₂ ∪ s₃ ∪ s₅).ncard
    _ = s₇.ncard + (s₂ ∪ s₃ ∪ s₅).ncard := by 
      apply Set.ncard_union_add_ncard_inter
      -- show that s₇.finite
      . simp [autoParam]
        apply Set.finite_of_ncard_pos
        rw [ncard_7]
        norm_num
      -- show that (s₂ ∪ s₃ ∪ s₅).finite
      . simp [autoParam]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        all_goals apply Set.finite_of_ncard_pos
        rw [ncard_2]; norm_num
        rw [ncard_3]; norm_num
        rw [ncard_5]; norm_num
    _ = s₇.ncard + ((s₅ ∪ (s₂ ∪ s₃)).ncard + (s₅ ∩ (s₂ ∪ s₃)).ncard) := by rw [disjoint5]; simp; rw [Set.union_comm]
    -- exactly calculate that (s₅ ∪ (s₂ ∪ s₃)).ncard + (s₅ ∩ (s₂ ∪ s₃)).ncard = s₅.ncard + (s₂ ∪ s₃).ncard
    _ = s₇.ncard + (s₅.ncard + (s₂ ∪ s₃).ncard) := by
      congr 1
      apply Set.ncard_union_add_ncard_inter
      -- show that s₅.finite
      . simp [autoParam]
        apply Set.finite_of_ncard_pos
        rw [ncard_5]
        norm_num
      -- show that (s₂ ∪ s₃).finite
      . simp [autoParam]
        refine ⟨?_, ?_⟩
        all_goals apply Set.finite_of_ncard_pos
        rw [ncard_2]; norm_num
        rw [ncard_3]; norm_num
    -- finally split (s₂ ∪ s₃).ncard = (s₂.ncard + s₃.ncard) - (s₂ ∩ s₃).ncard
    _ = s₇.ncard + (s₅.ncard + ((s₂.ncard + s₃.ncard) - (s₂ ∩ s₃).ncard)) := by 
      congr 2
      rw [<-@Set.ncard_union_add_ncard_inter]
      rw [Nat.add_sub_cancel]
      -- show that s₂.finite
      . simp [autoParam]
        apply Set.finite_of_ncard_pos
        rw [ncard_2]
        norm_num
      -- show that s₃.finite
      . simp [autoParam]
        apply Set.finite_of_ncard_pos
        rw [ncard_3]
        norm_num
    _ = s₇.ncard + s₅.ncard + (s₂.ncard + s₃.ncard - s₆.ncard) := by rw [inter23]; ring_nf
    _ = 19 := by rw [ncard_2, ncard_3, ncard_5, ncard_6, ncard_7]