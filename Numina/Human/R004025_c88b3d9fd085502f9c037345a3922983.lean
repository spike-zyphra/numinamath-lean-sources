import Mathlib

/- 9.3. Find all prime numbers $p$ for which $p^{2}+200$ is a perfect square of an integer. -/
theorem number_theory_230771 (p : ℕ) (hp : Nat.Prime p) :
    (∃ m : ℤ, m^2 = (p^2 + 200 : ℕ)) ↔ p = 5 ∨ p = 23
  := by
    constructor
    · intro h
      -- If a number is equal to the perfect square of an integer, then it's equal to
      -- the square of some natural number, so we don't have to consider negative integers
      obtain ⟨a, ha⟩ : ∃ a : ℕ, a ^ 2 = p ^ 2 + 200 := by
        obtain ⟨m, mh⟩ := h
        -- If m is an integer then m ^ 2 = |m| ^ 2, so we use |m| as our natural number
        refine ⟨m.natAbs, ?_⟩
        apply_fun (@Nat.cast ℤ _) using CharZero.cast_injective
        simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs, Nat.cast_add, Nat.cast_ofNat]
        exact mh
      clear h

      -- 2 ≠ 0
      have ne_zero : 2 ≠ 0 := by decide

      -- p is either even or odd
      cases' Nat.even_or_odd p with p1 p2
      -- even prime must be 2, so p = 2
      · have p_two : p = 2 := (Nat.Prime.even_iff hp).mp p1

        -- so a ^ 2 = 204
        rw [p_two] at ha
        simp only [Nat.reducePow, Nat.reduceAdd] at ha

        -- And we have 14 ^ 2 = 196 < 204 = a ^ 2 = 204 < 225 = 15 ^ 2
        have sq_14 : 14 ^ 2 = 196 := by decide
        have sq_15 : 15 ^ 2 = 225 := by decide
        have gt : 196 < 204 := by decide
        have lt : 204 < 225 := by decide
        rw [←ha] at gt lt
        rw [←sq_14] at gt
        rw [←sq_15] at lt

        -- but that means that 14 < a < 15
        have smono_lt := (Nat.pow_lt_pow_iff_left ne_zero).mp lt
        have smono_gt := (Nat.pow_lt_pow_iff_left ne_zero).mp gt
        -- contradiction
        linarith only [smono_lt, smono_gt]
      -- if p is odd, then a is odd
      · have a_odd : Odd a := by
          have a_sq_odd : Odd (a ^ 2) := by
            rw [ha]
            refine Nat.odd_add.mpr ?_
            simp only [Odd.pow p2, true_iff]
            decide
          exact Nat.Odd.of_mul_right a_sq_odd
        -- p is less than a
        have p_le : p < a := by
          have p_sq_le : p ^ 2 < a ^ 2 := by linarith
          exact (Nat.pow_lt_pow_iff_left ne_zero).mp p_sq_le

        -- we have (a + p) * (a - p) = 200
        have split : (a + p) * (a - p) = 200 := by
          rw [mul_comm, mul_add, Nat.sub_mul, Nat.sub_mul]
          convert_to a * a - p * a + (p * a - p * p) = 200
          congr 2
          · exact Nat.mul_comm a p
          · convert_to a * a - p * p = 200
            · refine Nat.sub_add_sub_cancel ?_ ?_
              · refine Nat.mul_le_mul_right a ?_
                exact Nat.le_of_succ_le p_le
              · refine Nat.mul_le_mul_left p ?_
                exact Nat.le_of_succ_le p_le
            ring_nf
            exact (Nat.eq_sub_of_add_eq' ha.symm).symm

        -- We express the choices of (a - p, a + p) = (a, b) as a finite set, where a * b = 200, a and b are even, and a < b.
        -- Given that a * b = 200, we use b = 200 / a, so that we only need to consider 200 numbers
        let choices := ((Finset.Icc 1 200).filter
          (fun x => x * (200 / x) = 200 ∧ Even x ∧ Even (200 / x) ∧ x < (200 / x))
          ).image (fun x => (⟨x, 200 / x⟩ : ℕ × ℕ))

        -- (a - p, a + p) has all those properties
        have mem : ⟨a - p, a + p⟩ ∈ choices := by
          unfold choices
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc, Prod.mk.injEq]
          refine ⟨a-p, ?_⟩
          -- 200 / (a - p) = (a + p)
          have div_eq : 200 / (a - p) = (a + p) := by
            rw [←split]
            have ne_zero : (a - p) ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr p_le
            exact (Nat.eq_div_of_mul_eq_left ne_zero rfl).symm
          rw [div_eq]
          refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩
          -- 1 ≤ a - p
          · omega
          -- a - p ≤ 200
          · rw [←split]
            refine Nat.le_mul_of_pos_left (a - p) ?_
            omega
          -- (a - p) * (a + p) = 200
          · exact mul_comm (a + p) (a - p) ▸ split
          -- Even (a - p)
          · exact Nat.Odd.sub_odd a_odd p2
          -- Even (a + p)
          · exact a_odd.add_odd p2
          -- a - p < a + p
          · rw [Nat.sub_lt_iff_lt_add (Nat.le_of_succ_le p_le)]
            ring_nf
            refine Nat.lt_add_of_pos_left ?_
            -- p is positive, because it's a prime
            have : 0 < p := Nat.Prime.pos hp
            -- so p ^ 2 os positive
            positivity

        -- but there are only three pairs of numbers which have all those properties
        have choices_eq : choices = {(2, 100), (4, 50), (10, 20)} := by decide

        -- so a - p and a + p have finite possibilities
        simp only [choices_eq, Finset.mem_insert, Prod.mk.injEq, Finset.mem_singleton] at mem

        -- a - p as naturals = a - p as integers, used by linarith procedure
        have z_sub : (((a - p) : ℕ) : ℤ) = (a : ℤ) - (p : ℤ) := by
          rw [Nat.cast_sub]
          -- because p ≤ a
          exact Nat.le_of_succ_le p_le

        -- we just have three cases left, so we check each individually
        rcases mem with ⟨h1, h2⟩ | ⟨h3, h4⟩ | ⟨h5, h6⟩
        -- a - p = 2 ∧ a + p = 100 means p = 49
        · have p_eq : p = 49 := by linarith only [z_sub, h1, h2]
          -- but 49 isn't prime
          have not_prime : ¬Nat.Prime 49 := by decide
          -- contradiction
          exact absurd (p_eq ▸ hp) not_prime
        -- a - p = 4 ∧ a + p = 50 means p = 23
        · have p_eq : p = 23 := by linarith only [z_sub, h3, h4]
          exact Or.inr p_eq
        -- a - p = 10 ∧ a + p = 20 means p = 23
        · have p_eq : p = 5 := by linarith only [z_sub, h5, h6]
          exact Or.inl p_eq

    · intro h
      -- p = 5 and p = 23 are valid solutions
      rcases h with h1 | h2
      · rw [h1]
        exact ⟨15, by norm_num⟩
      · rw [h2]
        exact ⟨27, by norm_num⟩