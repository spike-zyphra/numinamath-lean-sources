import Mathlib

/-Compute the sum of all two-digit positive integers
x such that for all three-digit (base 10) positive integers
abc, if abc is a multiple of x, then the three-digit (base 10) number bca
is also a multiple of x-/

theorem number_theory_610694: ∑ᶠ x ∈ {x: ℕ | 10 ≤ x ∧ x < 100 ∧
  ∀ a b c, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ x ∣ 100 * a + 10 * b + c →
    x ∣ 100 * b + 10 * c + a}, x = 64 := by

  -- We directly compute the set
    have h_eq: {x: ℕ | 10 ≤ x ∧ x < 100 ∧
  ∀ a b c, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ x ∣ 100 * a + 10 * b + c →
    x ∣ 100 * b + 10 * c + a} = {37, 27} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      -- the forward direction
      .
        intro h
        rcases h with ⟨lx1, lx2, h⟩
        simp

        -- we show that x ∣ 999
        have dx: x ∣ 999 := by

          -- we first find k such that 100 ≤ kx < 200
          have hk: ∃ k, 100 ≤ k * x ∧ k * x < 200 := by
            -- we enumerate by value of x
            have o: (10 ≤ x ∧ x < 20) ∨ (20 ≤ x ∧ x < 30) ∨ (30 ≤ x ∧ x < 50) ∨ (50 ≤ x ∧ x < 100):= by omega
            rcases o with o | o | o | o
            .
              use 10
              rcases o with ⟨o1, o2⟩
              constructor
              .
                omega
              .
                omega
            .
              use 5
              rcases o with ⟨o1, o2⟩
              constructor
              .
                omega
              .
                omega
            .
              use 4
              rcases o with ⟨o1, o2⟩
              constructor
              .
                omega
              .
                omega
            .
              use 2
              rcases o with ⟨o1, o2⟩
              constructor
              .
                omega
              .
                omega
                
          obtain ⟨k, hk⟩ := hk
          rcases hk with ⟨hk1, hk2⟩
          set d:= k * x - 100 with hd
          have ld1: 0 ≤ d := by simp [d]
          have ld2: d < 100 := by simp [d]; omega
          set b:= d / 10
          set c:= d % 10
          have od: d = 10 * b + c := by
            omega
          have lb1: 0 ≤ b := by
            simp [b]
          have lb2: b ≤ 9 := by
            simp [b]
            omega
          have lc1: 0 ≤ c := by
            simp [c]
          have lc2: c ≤ 9 := by
            simp [c]
            omega
          specialize h 1 b c
          norm_num at h
          simp [lb1, lb2, lc1, lc2] at h
          have f: x ∣ 100 + 10 * b + c := by
            rw [show 100 + 10 * b + c = 100 + (10 * b + c) by ring]
            rw [← od, hd]
            rw [show 100 + (k * x - 100) = k * x by omega]
            simp
          simp [f] at h
          have eq: 999 = 10 * (100 + 10 * b + c) - (100 * b + 10 * c + 1) := by
            omega
          rw [eq]
          apply Nat.dvd_sub
          omega
          have o1: (100 + 10 * b + c) ∣ 10 * (100 + 10 * b + c) := by
            simp
          apply dvd_trans f o1
          exact h

        -- then we conclude that x = 27 or x = 37
        replace dx: x ∈ Nat.divisors 999 := by
          simp
          exact dx
        have o: Nat.divisors 999 = {1, 3, 9, 27, 37, 111, 333, 999} := by
          native_decide
        rw [o] at dx
        clear o
        simp at dx
        rcases dx with g | g | g | g | g | g | g | g
        all_goals omega

      .
        intro h
        simp at h
        rcases h with h | h

        -- x = 37
        .
          simp [h]
          clear h
          intro a b c la1 la2 lb lc h
          have eq: 100 * b + 10 * c + a = 10 * (100 * a + 10 * b + c) - 999 * a := by
            omega
          rw [eq]
          apply Nat.dvd_sub
          omega
          have o1: (100 * a + 10 * b + c) ∣ 10 * (100 * a + 10 * b + c) := by
            simp
          apply dvd_trans h o1
          have o2: 37 ∣ 999 := by omega
          have o3: 999 ∣ 999 * a := by
            simp
          apply dvd_trans o2 o3

        -- x = 27
        .
          simp [h]
          clear h
          intro a b c la1 la2 lb lc h
          have eq: 100 * b + 10 * c + a = 10 * (100 * a + 10 * b + c) - 999 * a := by
            omega
          rw [eq]
          apply Nat.dvd_sub
          omega
          have o1: (100 * a + 10 * b + c) ∣ 10 * (100 * a + 10 * b + c) := by
            simp
          apply dvd_trans h o1
          have o2: 27 ∣ 999 := by omega
          have o3: 999 ∣ 999 * a := by
            simp
          apply dvd_trans o2 o3


  -- finally, we compute the sum
    rw [h_eq]
    rw [finsum_mem_eq_toFinset_sum]
    simp