import Mathlib

open Real

/- (a) Prove that for every positive integer $n$, there exists a fraction $\frac{a}{b}$ where $a$ and $b$ are integers satisfying $0< b \leqslant \sqrt{n}+1$ and $\sqrt{n} \leqslant \frac{a}{b} \leqslant \sqrt{n+1}$. (b) Prove that there are infinitely many positive integers $n$ such that there is no fraction $\frac{a}{b}$ where $a$ and $b$ are integers satisfying $0< b \leqslant \sqrt{n}$ and $\sqrt{n} \leqslant \frac{a}{b} \leqslant \sqrt{n+1}$. -/
theorem number_theory_24742 :
    (∀ n : ℕ, 0 < n → ∃ a b : ℤ, 0 < b ∧ b ≤ sqrt n + 1 ∧ sqrt n ≤ (a / b) ∧ (a / b) ≤ sqrt (n + 1)) ∧
    {n : ℕ | 0 < n ∧ ¬∃ a b : ℤ, 0 < b ∧ b ≤ sqrt n ∧ sqrt n ≤ (a / b) ∧ (a / b) ≤ sqrt (n + 1)}.Infinite := by

    constructor
    · -- part (a)
      intro n npos
      -- Let r be the unique positive integer for which r^2 ≤ n < (r + 1)^2
      let r := ⌊√n⌋
      have h_n_ge_1 : n ≥ 1 := npos
      have : √ n ≥ 1 := by
        refine one_le_sqrt.mpr ?_
        norm_cast
      have hr_ge_1 : r ≥ 1 := by
        refine Int.le_floor.mpr ?_
        norm_cast

      have : r ≤ √n := by exact Int.floor_le √n
      have h_n_ge_r_sq : r ^ 2 ≤ n := by
        suffices h : r ^ 2 ≤ (n : ℝ) by norm_cast at h
        rw [show n = √n ^ 2 by symm; apply sq_sqrt (by norm_cast; exact le_of_lt npos)]
        apply sq_le_sq'
        · trans 0
          simp; norm_cast; exact Int.le_of_lt hr_ge_1
        exact this

      have : r + 1 > √n := by exact Int.lt_floor_add_one √n
      have h_n_lt_r_add_1_sq : (r + 1) ^ 2 > n := by
        suffices h : (r + 1) ^ 2 > (n : ℝ) by norm_cast at h
        rw [show n = √n ^ 2 by symm; apply sq_sqrt (by norm_cast; exact le_of_lt npos)]
        apply sq_lt_sq'
        · trans 0
          simp; trans 0; norm_num; norm_cast
          linarith
        exact this

      -- write n = r ^ 2 + s
      let s := n - r ^ 2
      have h_n_rs : (n : ℝ) = r ^ 2 + s := by norm_cast; unfold s; ring
      -- then we have 0 ≤ s ≤ 2r
      have h_s_nonneg : 0 ≤ s := by exact Int.sub_nonneg_of_le h_n_ge_r_sq
      have h_s_le_2r : s ≤ 2 * r := by
        calc
          s = n - r ^ 2 := by unfold s; rfl
          _ ≤ (r + 1) ^ 2 - 1 - r ^ 2 := by simp; exact Int.le_sub_one_of_lt h_n_lt_r_add_1_sq
          _ = 2 * r := by ring

      -- we discuss in two cases according to the parity of s
      by_cases parity_s : Even s
      · -- case 1. s is even
        -- Consider the number (r + s / (2r))^2, we find that n = r^2 + s ≤ (r + s / (2r))^2
        have h1 : (n : ℝ) ≤ (r + s / (2 * r)) ^ 2 := by
          rw [h_n_rs, add_pow_two]
          have : (2 : ℝ) * r * (s / (2 * r)) = s := by field_simp
          rw [this]
          simp
          exact sq_nonneg (s / (2 * r : ℝ))
        -- and (r + s / (2r))^2 ≤ r^2 + s + 1 = n + 1
        have h2 : (r + s / (2 * r)) ^ 2 ≤ (n + 1 : ℝ) := by
          calc
            (r + s / (2 * r)) ^ 2 = (r ^ 2 + s + (s / (2 * r)) ^ 2 : ℝ) := by
              rw [add_pow_two]; field_simp
            _ = n + (s / (2 * r)) ^ 2 := by congr; symm; exact h_n_rs
            _ ≤ n + 1 ^ 2 := by
              simp
              have : |(s / (2 * r) : ℝ)| = s / (2 * r) := by
                apply abs_eq_self.mpr
                apply div_nonneg
                · norm_cast
                simp; linarith
              rw [this]
              have : 2 * r > (0 : ℝ) := by simp; linarith
              apply div_le_one (this) |>.mpr
              norm_cast
            _ = n + 1 := by ring
        -- It follows that √n ≤ r + s / (2r) ≤ √(n + 1)
        have h3 : √n ≤ r + s / (2 * r) := by
          have : √n = |√n| := by symm; apply abs_eq_self.mpr; exact sqrt_nonneg n
          rw [this]
          have : (r + s / (2 * r) : ℝ) = |(r + s / (2 * r) : ℝ)| := by
            symm
            apply abs_eq_self.mpr
            apply add_nonneg
            · norm_cast; linarith
            apply div_nonneg
            · norm_cast
            simp; linarith
          rw [this]
          apply sq_le_sq.mp
          rw [sq_sqrt]
          exact h1
          exact Nat.cast_nonneg' n
        have h4 : r + s / (2 * r) ≤ √(n + 1) := by
          have : √(n + 1) = |√(n + 1)| := by symm; apply abs_eq_self.mpr; exact sqrt_nonneg (n + 1)
          rw [this]
          have : (r + s / (2 * r) : ℝ) = |(r + s / (2 * r) : ℝ)| := by
            symm
            apply abs_eq_self.mpr
            apply add_nonneg
            · norm_cast; linarith
            apply div_nonneg
            · norm_cast
            simp; linarith
          rw [this]
          apply sq_le_sq.mp
          rw [sq_sqrt]
          exact h2
          norm_cast
          linarith

        -- since s is even, we can choose the freaction r + s/(2r) = (r^2 + s/2) / r
        have ⟨k, hk⟩ := parity_s
        use (r ^ 2 + k), r
        constructor
        · exact hr_ge_1
        constructor
        · linarith
        have : ((↑(r ^ 2 + k) / r) : ℝ) = r + s / (2 * r) := by
          rw [hk]
          field_simp
          ring
        rw [this]
        constructor
        · exact h3
        · exact h4

      · -- case 2. s is odd
        apply Int.not_even_iff_odd.mp at parity_s
        -- consider the number (r + 1 - (2r + 1 - s) / (2(r+1)))^2 = (r + 1)^2 - (2r+1-s) + ((2r + 1 - s) / (2(r+1)))^2
        -- we find that (r + 1)^2 - (2r+1-s) + ((2r + 1 - s) / (2(r+1)))^2 = r^2 + s + ((2r + 1 - s) / (2(r+1)))^2 ≥ n
        have h1 : n ≤ (r + 1 - ((2 * r + 1 - s) / (2 * (r + 1)) : ℝ)) ^ 2 := by
          rw [sub_pow_two]
          have : ((r + 1) ^ 2 - 2 * (r + 1) * ((2 * r + 1 - s) / (2 * (r + 1))) : ℝ) = r ^ 2 + s := by
            field_simp; ring
          rw [this, h_n_rs]
          simp; exact sq_nonneg ((2 * r + 1 - s) / (2 * (r + 1)) : ℝ)

        -- and that (r + 1 - (2r + 1 - s) / (2(r+1)))^2 ≤ (r + 1)^2 - (2r + 1 - s) + 1 = n + 1
        have h2 : (r + 1 - ((2 * r + 1 - s) / (2 * (r + 1)) : ℝ)) ^ 2 ≤ n + 1 := by
          trans (r + 1) ^ 2 - (2 * r + 1 - s) + 1
          · rw [sub_pow_two]
            have : (2 * (r + 1) * ((2 * r + 1 - s) / (2 * (r + 1))) : ℝ) = (2 * r + 1 - s) := by field_simp
            rw [this]
            simp
            have h3 : (2 * r + 1 - s : ℝ) > 0 := by norm_cast; linarith
            have h4 : (2 * (r + 1) : ℝ) > 0 := by norm_cast; linarith
            have : (2 * r + 1 - s : ℝ) / (2 * (r + 1) : ℝ) > 0 := by apply div_pos; assumption; assumption
            rw [abs_eq_self.mpr]
            apply div_le_one h4 |>.mpr
            norm_cast
            linarith
            apply le_of_lt
            exact this
          have : ((r + 1) ^ 2 - ((2 * r + 1 - s)) : ℝ) = r ^ 2 + s := by ring
          rw [this, h_n_rs]

        have h3 : √n ≤ (r + 1 - ((2 * r + 1 - s) / (2 * (r + 1)) : ℝ)) := by
          have : √n = |√n| := by symm; apply abs_eq_self.mpr; exact sqrt_nonneg ↑n
          rw [this]
          have : (r + 1 - (2 * r + 1 - s) / (2 * (r + 1)) : ℝ) = |(r + 1 - (2 * r + 1 - s) / (2 * (r + 1)) : ℝ)| := by
            symm
            apply abs_eq_self.mpr
            have h3 : (2 * r + 1 - s : ℝ) > 0 := by norm_cast; linarith
            have h4 : (2 * (r + 1) : ℝ) > 0 := by norm_cast; linarith
            have : (2 * r + 1 - s : ℝ) / (2 * (r + 1)) ≤ 1 := by
              apply div_le_one h4 |>.mpr
              norm_cast
              linarith
            linarith
          rw [this]
          apply sq_le_sq.mp
          rw [sq_sqrt]
          exact h1
          exact Nat.cast_nonneg' n

        have h4 : √(n + 1) ≥ (r + 1 - ((2 * r + 1 - s) / (2 * (r + 1)) : ℝ)) := by
          have : √(n + 1) = |√(n + 1)| := by symm; apply abs_eq_self.mpr; exact sqrt_nonneg (n + 1)
          rw [this]
          have : (r + 1 - (2 * r + 1 - s) / (2 * (r + 1)) : ℝ) = |(r + 1 - (2 * r + 1 - s) / (2 * (r + 1)) : ℝ)| := by
            symm
            apply abs_eq_self.mpr
            have h3 : (2 * r + 1 - s : ℝ) > 0 := by norm_cast; linarith
            have h4 : (2 * (r + 1) : ℝ) > 0 := by norm_cast; linarith
            have : (2 * r + 1 - s : ℝ) / (2 * (r + 1)) ≤ 1 := by
              apply div_le_one h4 |>.mpr
              norm_cast
              linarith
            linarith
          rw [this]
          apply sq_le_sq.mp
          rw [sq_sqrt]
          exact h2
          linarith

        -- since s is odd, we can choose the fraction r + 1 - (2r + 1 - s) / (2(r+1)) = ((r + 1)^2 - r + (s-1) / 2) / (r + 1)
        have ⟨k, hk⟩ := parity_s
        use (r + 1) ^ 2 - r + k, r + 1
        constructor
        · linarith
        constructor
        · simp; exact Int.floor_le √↑n

        have : (((r + 1) ^ 2 - r + k : ℤ)) / (↑(r + 1) : ℝ) = (r + 1 - ((2 * r + 1 - s) / (2 * (r + 1)) : ℝ)) := by
          rw [hk]
          field_simp
          ring
        rw [this]
        constructor
        · exact h3
        · exact h4
    · -- part (b)
      -- we show that for every positive integer r, there is no fraction a / b with b ≤ √(r^2 + 1) and √(r^2 + 1) ≤ a/b ≤ √(r^2 + 2).

      let f : ℕ → ℕ := fun n ↦ (n + 1) ^ 2 + 1
      have : Function.Injective f := by
        intro x y heq
        unfold f at heq
        simp at heq
        exact heq
      apply Set.infinite_of_injective_forall_mem this

      intro r'; unfold f
      generalize h : r' + 1 = r

      have r_pos : r > 0 := by rw [← h]; linarith

      -- clearly every r^2 + 1 is positive
      constructor
      exact Nat.zero_lt_succ (r ^ 2)

      -- suppose on the contrary that such a fraction a/b exists
      rintro ⟨a, b, bpos, b_le, h1, h2⟩

      have a_nonneg : a ≥ 0 := by
        have : (a / b : ℝ) ≥ 0 := by
          trans √(r ^ 2 + 1 : ℕ)
          · exact h1
          simp
        norm_cast at this
        exact (Rat.divInt_nonneg_iff_of_pos_right bpos).mp this


      -- Since b ≤ √(r^2 + 1) < r + 1
      have h3 : √(r ^ 2 + 1) < r + 1 := by
        refine (sqrt_lt' ?hy).mpr ?_
        · linarith
        rw [add_pow_two]
        simp [r_pos]

      -- and b is an integer, we have b ≤ r
      have h_b_le_r: b ≤ r := by
        suffices h : (b : ℝ) < r + 1 by
          norm_cast at h
          exact Int.lt_add_one_iff.mp h
        calc
          b ≤ √(r ^ 2 + 1) := by norm_cast
          _ < r + 1 := by exact h3

      -- Hence, (1), (br)^2 < b^2 (r^2 + 1) ≤ a^2
      have h_a_sq_ge : (b * r) ^ 2 < a ^ 2 := by

        calc
          (b * r) ^ 2 < b ^ 2 * (r ^ 2 + 1) := by
            rw [mul_pow, mul_add]
            simp; apply pow_pos; exact bpos
          _ ≤ a ^ 2 := by
            have : √(r ^ 2 + 1 : ℕ) = |√(r ^ 2 + 1)| := by
              symm
              norm_cast
              apply abs_eq_self.mpr
              simp
            rw [this] at h1

            have : (a / b : ℝ) = |(a / b : ℝ)|:= by
              symm
              apply abs_eq_self.mpr
              apply div_nonneg
              exact Int.cast_nonneg.mpr a_nonneg
              norm_cast; exact Int.le_of_lt bpos
            rw [this] at h1

            apply sq_le_sq.mpr at h1
            rw [sq_sqrt, div_pow] at h1
            rw [le_div_iff₀, mul_comm] at h1
            norm_cast at h1

            norm_cast
            apply pow_pos
            exact bpos

            norm_cast; simp

      -- so a > br
      have : a > b * r := by
        have : a = |a| := by symm; apply abs_eq_self.mpr; exact a_nonneg
        rw [this]
        have : b * r = |b * r| := by
          symm
          apply abs_eq_self.mpr
          apply mul_nonneg
          exact Int.le_of_lt bpos
          exact Int.ofNat_zero_le r
        rw [this]
        exact sq_lt_sq.mp h_a_sq_ge

      -- and (2), a^2 ≤ b^2 (r^2 + 2) < (br + 1)^2
      have h_a_sq_le : a ^ 2 < (b * r + 1) ^ 2 := by
        calc
          a ^ 2 ≤ b ^ 2 * (r ^ 2 + 2) := by
            simp at h2
            rw [add_assoc, show (1 + 1 : ℝ) = 2 by ring] at h2

            have : (a / b : ℝ) = |(a / b : ℝ)|:= by
              symm
              apply abs_eq_self.mpr
              apply div_nonneg
              exact Int.cast_nonneg.mpr a_nonneg
              norm_cast; exact Int.le_of_lt bpos
            rw [this] at h2

            have : √(r ^ 2 + 2 : ℝ) = |√(r ^ 2 + 2)| := by
              symm
              norm_cast
              apply abs_eq_self.mpr
              simp
            rw [this] at h2

            apply sq_le_sq.mpr at h2
            rw [sq_sqrt, div_pow] at h2
            rw [div_le_iff₀, mul_comm] at h2
            norm_cast at h2

            · norm_cast;
              apply pow_pos
              exact bpos

            norm_cast; simp

          _ < (b * r + 1) ^ 2 := by
            rw [mul_add, add_pow_two, mul_pow, add_assoc]
            simp
            rw [mul_comm, ← mul_assoc]
            suffices h : 2 * b ^ 2 ≤ 2 * b * r by linarith
            rw [pow_two, ← mul_assoc]
            refine Int.mul_le_mul_of_nonneg_left h_b_le_r ?h₂
            simp
            exact Int.le_of_lt bpos

      -- so a < br + 1
      have : a < b * r + 1 := by
        have : a = |a| := by symm; apply abs_eq_self.mpr; exact a_nonneg
        rw [this]
        have : b * r + 1 = |b * r + 1| := by
          symm
          apply abs_eq_self.mpr
          apply add_nonneg
          apply mul_nonneg
          exact Int.le_of_lt bpos
          exact Int.ofNat_zero_le r
          norm_num
        rw [this]
        exact sq_lt_sq.mp h_a_sq_le

      -- but br < a < br + 1 is impossible
      linarith
