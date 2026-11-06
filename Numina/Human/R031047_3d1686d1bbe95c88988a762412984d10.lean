import Mathlib

/- Déterminer tous les triplets d'entiers $(\mathfrak{a}, \mathfrak{b}, \mathfrak{n}$ ) strictement positifs vérifiant:

$$
a!+b!=2^{n}
$$ -/

theorem number_theory_607295: {(a, b, n): ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < n ∧ a.factorial + b.factorial = 2 ^ n} =
    {(1, 1, 1), (2, 2, 2), (2, 3, 3), (3, 2, 3)} := by

    ext ⟨a, b, n⟩
    constructor
    -- the forward direction
    .
      simp only [Set.mem_setOf_eq]
      intro h
      simp
      rcases h with ⟨ha, hb, hn, h⟩

      -- we first show that a or b is less than 3 by mod 3
      have l: a ≤ 2 ∨ b ≤ 2 := by
        by_contra! l
        have la: 3 ≤ a := by omega
        have lb: 3 ≤ b := by omega
        clear l
        have da: 3 ∣ a.factorial := by
          apply Nat.dvd_factorial
          norm_num
          exact la
        have db: 3 ∣ b.factorial := by
          apply Nat.dvd_factorial
          norm_num
          exact lb
        have c: 3 ∣ 2 ^ n := by
          rw [← h]
          omega
        apply Nat.Prime.dvd_of_dvd_pow at c
        norm_num at c
        norm_num
      rcases l with l | l
      -- case 1: a ≤ 2
      .
        -- case a ≤ 2
        replace l: a = 1 ∨ a = 2 := by omega
        rcases l with l | l
        .
          -- case a = 1
          .
            simp [l] at *
            -- then we must have b = 1
            replace lb: b < 2 := by
              by_contra! lb
              have o: 2 ∣ b.factorial := by
                apply Nat.dvd_factorial
                norm_num
                exact lb
              have c: 2 ∣ 2 ^ n := by
                have eq: 2 ^ n = 2 * 2 ^ (n - 1) := by
                  nth_rewrite 1 [show n = n - 1 + 1 by omega]
                  ring
                rw [eq]
                omega
              rw [← h] at c
              have x: 2 ∣ 1 := by
                rw [show 1 = 1 + b.factorial - b.factorial by omega]
                apply Nat.dvd_sub
                omega
                omega
                omega
              norm_num at x
            have r: b = 1 := by omega
            simp [r] at *
            symm at h
            rw [Nat.pow_eq_self_iff] at h
            exact h
            norm_num
        .
          -- case a = 2

          simp [l] at *
          -- then we must have b ≤ 3
          replace lb: b < 4 := by
            by_contra! lb
            by_cases ln: n = 1
            -- case n = 1
            .
              simp [ln] at h
              have o:= Nat.factorial_pos b
              rw [h] at o
              norm_num at o
            .
              -- case n > 1
              replace ln: 2 ≤ n := by
                omega
              have d: 4 ∣ 2 ^ n := by
                have eq: 2 ^ n = 4 * 2 ^ (n - 2) := by
                  nth_rewrite 1 [show n = n - 2 + 2 by omega]
                  ring
                rw [eq]
                omega
              rw [← h] at d
              have i: 4 ∣ b.factorial := by
                apply Nat.dvd_factorial
                norm_num
                exact lb
              have c: 4 ∣ 2 := by
                rw [show 2 = 2 + b.factorial - b.factorial by omega]
                apply Nat.dvd_sub
                omega
                omega
                omega
              norm_num at c
          replace lb: b = 1 ∨ b = 2 ∨ b = 3 := by omega
          rcases lb with lb | lb | lb
          .
            simp [lb] at *
            have o: 2 ∣ 2 ^ n := by
              rw [show 2 ^ n = 2 * 2 ^ (n - 1) by
                nth_rewrite 1 [show n = n - 1 + 1 by omega]
                ring]
              omega
            rw [← h] at o
            have x: 2 ∣ 1 := by
              rw [show 1 = 1 + b.factorial - b.factorial by omega]
              apply Nat.dvd_sub
              omega
              omega
              omega
            norm_num at x
          .
            -- case b = 2
            simp [lb] at *
            rw [show 4 = 2 ^ 2 by omega] at h
            rw [pow_right_inj₀] at h
            omega
            norm_num
            norm_num
          .
            -- case b = 3
            simp [lb] at *
            have o: Nat.factorial 3 = 6 := by
              decide
            rw [o] at h
            norm_num at h
            rw [show 8 = 2 ^ 3 by omega] at h
            rw [pow_right_inj₀] at h
            omega
            norm_num
            norm_num
      .
        -- case b ≤ 2
        replace l: b = 1 ∨ b = 2 := by omega
        rcases l with l | l
        .
          -- case b = 1
          simp [l] at *
          -- then we must have a = 1
          replace la: a < 2 := by
            by_contra! la
            have o: 2 ∣ a.factorial := by
              apply Nat.dvd_factorial
              norm_num
              exact la
            have c: 2 ∣ 2 ^ n := by
              have eq: 2 ^ n = 2 * 2 ^ (n - 1) := by
                nth_rewrite 1 [show n = n - 1 + 1 by omega]
                ring
              rw [eq]
              omega
            rw [← h] at c
            have x: 2 ∣ 1 := by
              rw [show 1 = a.factorial + 1 - a.factorial by omega]
              apply Nat.dvd_sub
              omega
              omega
              omega
            norm_num at x
          have r: a = 1 := by omega
          simp [r] at *
          symm at h
          rw [Nat.pow_eq_self_iff] at h
          exact h
          norm_num
        .
          -- case b = 2

          simp [l] at *
          -- then we must have a ≤ 3
          replace la: a < 4 := by
            by_contra! la
            by_cases ln: n = 1
            -- case n = 1
            .
              simp [ln] at h
              have o:= Nat.factorial_pos a
              rw [h] at o
              norm_num at o
            .
              -- case n > 1
              replace ln: 2 ≤ n := by
                omega
              have d: 4 ∣ 2 ^ n := by
                have eq: 2 ^ n = 4 * 2 ^ (n - 2) := by
                  nth_rewrite 1 [show n = n - 2 + 2 by omega]
                  ring
                rw [eq]
                omega
              rw [← h] at d
              have i: 4 ∣ a.factorial := by
                apply Nat.dvd_factorial
                norm_num
                exact la
              have c: 4 ∣ 2 := by
                rw [show 2 = 2 + a.factorial - a.factorial by omega]
                apply Nat.dvd_sub
                omega
                omega
                omega
              norm_num at c
          replace la: a = 1 ∨ a = 2 ∨ a = 3 := by omega
          rcases la with la | la | la
          .
            -- case a = 1
            simp [la] at *
            have o: 2 ∣ 2 ^ n := by
              rw [show 2 ^ n = 2 * 2 ^ (n - 1) by
                nth_rewrite 1 [show n = n - 1 + 1 by omega]
                ring]
              omega
            rw [← h] at o
            have x: 2 ∣ 1 := by
              rw [show 1 = a.factorial + 1 - a.factorial by omega]
              apply Nat.dvd_sub
              omega
              omega
              omega
            norm_num at x
          .
            -- case a = 2
            simp [la] at *
            rw [show 4 = 2 ^ 2 by omega] at h
            rw [pow_right_inj₀] at h
            omega
            norm_num
            norm_num
          .
            -- case a = 3
            simp [la] at *
            have o: Nat.factorial 3 = 6 := by
              decide
            rw [o] at h
            norm_num at h
            rw [show 8 = 2 ^ 3 by omega] at h
            rw [pow_right_inj₀] at h
            omega
            norm_num
            norm_num


  -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h | h
      all_goals simp [h] at *
      .
        decide
      .
        decide
