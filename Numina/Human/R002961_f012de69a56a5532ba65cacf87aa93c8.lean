import Mathlib

/-5. Find the smallest positive integer $n$ such that among any $n$ chosen integers, there exist at least two integers whose sum or difference is divisible by 1997.-/
theorem number_theory_135430 :
  IsLeast
    {n : ℕ | n > 0 ∧
      ∀ s : Finset ℤ, s.card = n →
        ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ (1997 ∣ a + b ∨ 1997 ∣ a - b)}
    1000 := by

  constructor
  · -- we first show that n = 1000 works
    simp
    -- let S be any set of 1000 integers
    intro S hS_card

    let T : Finset ℤ := Finset.Icc 0 998
    have hT_card : T.card = 999 := by simp [T]

    -- we map a ∈ S to |a mod 1997| where the mod is balanced to -997, ..., 998
    let f : ℤ → ℤ := fun n ↦ |n.bmod 1997|

    have hf : ∀ a ∈ S, f a ∈ T := by
      intro a _
      simp [T, f]
      apply abs_le.mpr
      constructor
      all_goals rw [show (998 : ℤ) = 1997 / 2 by norm_num]
      · exact Int.le_bmod (by norm_num)
      · exact Int.bmod_le (by norm_num)

    have h_cards : T.card * 1 < S.card := by linarith

    -- there must be two elememts a, b ∈ S such that |a mod 1997| = |b mod 1997|
    have ⟨r, rmem, hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf h_cards

    apply Finset.one_lt_card.mp at hr
    obtain ⟨a, amem, b, bmem, a_ne_b⟩ := hr

    apply Finset.mem_filter.mp at amem
    apply Finset.mem_filter.mp at bmem

    use a, amem.1, b, bmem.1, a_ne_b

    have h_bmod_abs_eq : |a.bmod 1997| = |b.bmod 1997| := by
      simp [f] at amem bmem
      linarith only [amem, bmem]

    -- so either (a mod 1997) = (b mod 1997) or (a mod 1997) = -(b mod 1997)
    rcases abs_eq_abs.mp h_bmod_abs_eq with h_eq | h_eq_neg
    · -- in the first case, we have a ≡ b (mod 1997) so 1997 ∣ a - b
      right
      suffices h : a ≡ b [ZMOD 1997] by
        apply Int.modEq_iff_dvd.mp
        symm
        exact h
      unfold Int.ModEq
      rw [show (1997 : ℤ) = ↑(1997 : ℕ) by norm_cast]
      rw [← Int.bmod_emod]
      nth_rw 2 [← Int.bmod_emod]
      rw [h_eq]
    · -- in the second case, we have a ≡ -b (mod 1997) so 1997 ∣ a + b
      left
      apply Int.dvd_of_emod_eq_zero
      rw [Int.add_emod]
      rw [show (1997 : ℤ) = ↑(1997 : ℕ) by norm_cast]
      nth_rw 2 [← Int.bmod_emod]
      nth_rw 3 [← Int.bmod_emod]
      rw [h_eq_neg]
      norm_num
  · -- now we show that the solution n cannot be less than 1000
    intro n ⟨npos, hn⟩

    -- suppose on the contrary, n ≤ 999
    by_contra! h

    -- take S = 0, 1, ..., n - 1 ≤ 998
    let S : Finset ℤ := Finset.Icc 0 (n - 1)
    have hS_card : S.card = n := by simp [S]

    -- then there exists a, b ∈ S such that 1997 divides a + b or a - b
    obtain ⟨a, amem, b, bmem, a_ne_b, (h_dvd_add | h_dvd_sub)⟩ := hn S hS_card
    all_goals simp [S] at amem bmem
    · -- if 1997 ∣ a + b, then a + b ≥ 1997
      have h_sum_ge : a + b ≥ 1997 := by
        apply Int.le_of_dvd
        · by_contra! h_nonpos
          have : a = 0 := by linarith only [h_nonpos, amem.1, bmem.1]
          have : b = 0 := by linarith only [h_nonpos, amem.1, bmem.1]
          have : a = b := by
            trans 0
            assumption
            symm
            assumption
          contradiction
        · exact h_dvd_add

      -- but a + b ≤ 1996 as a, b, ≤ n - 1 ≤ 998
      have h_sum_le : a + b ≤ 1996 := by
        linarith only [amem.2, bmem.2, h]

      -- we get a contradiction
      linarith only [h_sum_ge, h_sum_le]
    · -- if 1997 ∣ a - b, we argue similarly
      obtain ⟨k, hk⟩ := h_dvd_sub
      have k_nz : k ≠ 0 := by
        intro k_eq
        simp [k_eq] at hk
        have : a = b := by exact Int.eq_of_sub_eq_zero hk
        contradiction
      by_cases kpos : k > 0
      · linarith
      push_neg at kpos
      have : k < 0 := by exact lt_of_le_of_ne kpos k_nz
      linarith
