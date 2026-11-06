import Mathlib

/-For how many integers a (1≤ a ≤ 200) is the number a ^ a a square?-/
theorem number_theory_611027: {a: ℕ | 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}.encard = 107 := by

 -- Firstly we count the odd and even numbers separately
  have h_odd_count: {a: ℕ | Odd a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}.encard = 7 := by
    -- we show that it's equivalent to a is square
    have h_eq: {a: ℕ | Odd a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}
     = {a: ℕ | Odd a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare a} := by
      ext a
      simp
      intro ha ha1 ha2
      apply Odd.exists_bit1 at ha
      obtain ⟨n,hn⟩ := ha
      constructor
      -- the forward direction
      . intro h
        nth_rewrite 2 [hn] at h
        rw [show a ^ (2 * n + 1) = a * a ^ (2 * n) by ring] at h
        rw [isSquare_iff_exists_sq]
        rw [isSquare_iff_exists_sq] at h
        obtain ⟨m,hm⟩ := h
        rw [show a ^ (2 * n) = (a ^ n) ^ 2 by ring] at hm
        set b:= a ^ n with hb
        clear_value b
        use m / b
        have d: b ^ 2 ∣ m ^ 2 := by
          rw [← hm]
          apply Nat.dvd_mul_left
        have d2: b ∣ m := by
          rw [Nat.pow_dvd_pow_iff] at d
          exact d
          norm_num
        have ne: (b: ℚ) ≠ 0 := by
            simp
            rw [hb]
            apply pow_ne_zero
            omega
        have ne2: (b: ℚ) ^ 2 ≠ 0 := by
            simp
            rw [hb]
            apply pow_ne_zero
            omega
        have eq1: (m / b) ^ 2 = m ^ 2 / b ^ 2 := by
          qify
          have t: ↑((m: ℤ) ^ 2 / b ^ 2) = (m: ℚ) ^ 2 / (b: ℚ) ^ 2 := by
            rw [Rat.intCast_div]
            simp
            zify at d
            exact d
          rw [t]
          field_simp [ne,ne2]
        rw [eq1]
        rw [← hm]
        qify
        field_simp
      -- the backward direction
      . intro h
        apply IsSquare.pow
        exact h
    -- Then we compute the new set directly
    rw [h_eq]
    have h_is: {a | Odd a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare a} = {1,9,25,49,81,121,169} := by
      ext a
      simp
      constructor
      . intro h
        rcases h with ⟨ha,ha1,ha2,h⟩
        rw [isSquare_iff_exists_sq] at h
        obtain ⟨r,hr⟩ := h
        have r1: 1 ≤ r := by nlinarith
        have d: ¬ 2 ∣ r := by
          by_contra! d
          have e: 2 ∣ a := by
            rw [hr]
            have d2: r ∣ r ^ 2 := by
              apply dvd_pow_self
              norm_num
            apply dvd_trans d d2
          rw [←even_iff_two_dvd] at e
          absurd ha
          simp
          exact e
        replace d: 2 ∣ r - 1 := by omega
        apply exists_eq_mul_right_of_dvd at d
        obtain ⟨s,hs⟩ := d
        replace hs: r = 2 * s + 1 := by
          omega
        simp [hs] at hr
        simp [hr]
        have hs: s ≤ 6 := by
          nlinarith
        clear * - hs
        interval_cases s <;> omega

      . intro h
        rcases h with h | h | h | h | h | h | h
        <;> simp [h]
        <;> clear *-
        <;> native_decide

    rw [h_is]
    simp [Set.encard]

  have h_even_count: {a: ℕ | Even a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}.encard = 100 := by
    -- we show that the set is exactly the set of even numbers
    have h_eq: {a: ℕ | Even a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}
    = (Finset.image (fun x => x * 2) (Finset.Icc 1 100)) := by
      ext a
      constructor
      -- the forward direction
      . intro h
        simp at h
        rcases h with ⟨ha,ha1,ha2,h⟩
        simp
        rw [even_iff_exists_two_mul] at ha
        obtain ⟨n,hn⟩ := ha
        use n
        constructor
        . simp [hn] at ha1 ha2
          omega
        . omega
      -- the backward direction
      . intro h
        simp at h
        obtain ⟨n,hn⟩ := h
        rcases hn with ⟨hn1,hn⟩
        rcases hn1 with ⟨hn1,hn2⟩
        rw [show n * 2 = 2 * n by ring] at hn
        simp
        constructor
        . rw [←hn]
          apply even_two_mul
        . constructor
          . omega
          . rw [← hn]
            constructor
            . omega
            . nth_rewrite 1 [hn]
              rw [show a ^ (2 * n) = (a ^ n) ^ 2 by ring]
              apply IsSquare.sq
    rw [h_eq]
    rw [Set.encard_coe_eq_coe_finsetCard]
    rw [Finset.card_image_of_injective]
    simp
    intro x y h
    simp at h
    exact h


-- Then we split the set into odd and even numbers
  have sum_card:
    {a: ℕ | 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}.encard
    = {a: ℕ | Odd a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}.encard + {a: ℕ | Even a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)}.encard := by
    have h_union:
      {a: ℕ | 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)} =
      {a: ℕ | Odd a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)} ∪ {a: ℕ | Even a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)} := by
        ext a
        simp
        constructor
        -- the forward direction
        . intro h
          simp [h]
          symm
          apply Nat.even_or_odd
        -- the backward direction
        . intro h
          rcases h with h | h
          . simp [h]
          . simp [h]
    have h_disjoint:
      Disjoint {a: ℕ | Odd a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)} {a: ℕ | Even a ∧ 1 ≤ a ∧ a ≤ 200 ∧ IsSquare (a ^ a)} := by
        rw [Set.disjoint_left]
        intro a h
        simp at h
        simp [h]
    rw [h_union]
    rw [Set.encard_union_eq h_disjoint]

-- Finally we combine the results
  rw [sum_card,h_odd_count,h_even_count]
  norm_num