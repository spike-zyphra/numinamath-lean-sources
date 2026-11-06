import Mathlib

/-How many positive even perfect cubes are less than 2008?-/
theorem algebra_19809 :
    Set.ncard {n : ℕ | Even n ∧ ∃ k, n = k^3 ∧ n < 2008 ∧ 0 < n} = 6 := by

  -- set f : n → 8 * n ^ 3
  let f : ℕ → ℕ := fun n ↦ (2 * n) ^ 3

  -- show that f is injective at Finset.Icc 1 6
  have inj_f : Set.InjOn f (Finset.Icc 1 6) := by
    intro n _ m _ feq
    simp [f] at feq
    exact feq

  -- show that image of f at Finset.Icc 1 6 is {n : ℕ | Even n ∧ ∃ k, n = k^3 ∧ n < 2008}
  have imf : f ''(Finset.Icc 1 6) = {n : ℕ | Even n ∧ ∃ k, n = k^3 ∧ n < 2008 ∧ 0 < n} := by
    ext n
    simp [f]
    -- divide into two parts
    apply Iff.intro <;> intro h

    -- when n ∈ f ''(Finset.Icc 1 6)
    . obtain ⟨m, ⟨hm1, hm2⟩, hn⟩ := h
      rw [<-hn]
      norm_num
      simp [Even]
      refine ⟨?_, ?_, ?_⟩

      -- show that Even n
      . use (4 * m ^ 3)
        ring_nf

      -- show that n < 2008
      . calc
          (2 * m) ^ 3 = 8 * m ^ 3 := by ring_nf
          _ ≤ 8 * 6 ^ 3 := by
            apply mul_le_mul
            norm_num
            pick_goal 3; norm_num
            . -- show that m ^ 3 ≤ 6 ^ 3
              apply Nat.pow_le_pow_of_le_left
              exact hm2
            -- show that 0 ≤ m ^ 3
            . positivity
          _ < 2008 := by norm_num

      -- show that 0 < n
      . positivity

    -- when n ∈ {n : ℕ | Even n ∧ ∃ k, n = k^3 ∧ n < 2008}
    . simp [Even] at h
      obtain ⟨⟨r, heven⟩, ⟨m, hm⟩, hn1, hn2⟩ := h

      -- show that 2 ∣ n
      replace heven : 2 ∣ n := by
        use r
        rw [heven]
        ring_nf

      -- show that 2 ∣ m
      rw [hm] at heven
      apply Nat.Prime.dvd_of_dvd_pow at heven
      pick_goal 2
      norm_num
      -- have m = 2t
      obtain ⟨t, ht⟩ := heven

      -- show that t is the answer
      use t
      refine ⟨⟨?_, ?_⟩, ?_⟩
      -- show that 1 ≤ t
      . cases t with
        | zero => -- when t = 0
          rw [hm, ht] at hn2
          norm_num at hn2
        | succ t => -- when t ≥ 1
          linarith only

      -- show that t ≤ 6
      . rw [hm, ht] at hn1
        -- have (2t)^3 < 13^3
        replace hn1 : (2 * t) ^ 3 < 13 ^ 3 := by
          calc
            (2 * t) ^ 3 < 2008 := by exact hn1
            _ < 13 ^ 3 := by norm_num
        -- show that 2t < 13
        rw [Nat.pow_lt_pow_iff_left] at hn1
        linarith only [hn1]
        norm_num
      -- show that (2t) ^ 3 = n
      . rw [hm, ht]

  calc
    {n : ℕ | Even n ∧ ∃ k, n = k^3 ∧ n < 2008 ∧ 0 < n}.ncard = (f ''(Finset.Icc 1 6)).ncard := by rw [imf]
    _ = (Finset.Icc 1 6 : Set ℕ).ncard := by apply Set.ncard_image_of_injOn; exact inj_f
    _ = (Finset.Icc 1 6).card := by rw [Set.ncard_coe_Finset]
    _ = 6 := by rw [Nat.card_Icc]
