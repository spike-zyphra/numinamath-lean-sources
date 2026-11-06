import Mathlib

set_option maxHeartbeats 800000
/-Find the number of ordered triples of nonnegative integers (a,b,c) that satisfy
(a * b + 1) * (b * c + 1) * (c * a + 1) = 84-/
theorem number_theory_609671: {(a, b, c): ℕ × ℕ × ℕ | (a * b + 1) * (b * c + 1) * (c * a + 1) = 84}.encard = 12 := by

 -- We will directly compute the set --
  have set_eq: {(a, b, c): ℕ × ℕ × ℕ | (a * b + 1) * (b * c + 1) * (c * a + 1) = 84}
   = {(0,1,83),(1,83,0),(83,0,1),(0,83,1),(83,1,0),(1,0,83),(1,2,3),(1,3,2),(2,1,3),(2,3,1),(3,1,2),(3,2,1)} := by
    ext ⟨a, b, c⟩
    constructor
    -- the forward direction --

    . intro h
      simp at h
      simp
      by_contra! ne -- for convenience, use contra --
      -- we show that a ≠ 0 --
      have ha: a ≠ 0 := by
        by_contra! ha
        rw [ha] at h
        simp at h
        replace h: b * c = 83 := by omega
        have db: b ∣ 83 := by rw [← h]; simp
        rw [Nat.Prime.dvd_iff_eq] at db
        simp [← db] at h
        symm at db
        absurd ne
        simp [ha,db,h]
        norm_num
        by_contra! b_val -- if b = 1 --
        simp [b_val] at h
        simp [ha,b_val,h] at ne
      -- similarly, we show that b ≠ 0 --
      have hb: b ≠ 0 := by
        by_contra! hb
        rw [hb] at h
        simp at h
        have da: a ∣ 83 := by rw [← h]; simp
        rw [Nat.Prime.dvd_iff_eq] at da
        simp [← da] at h
        symm at da
        absurd ne
        simp [hb,da,h]
        norm_num
        by_contra! c_val -- if c = 1 --
        simp [c_val] at h
        simp [hb,c_val,h] at ne
      -- similarly, we show that c ≠ 0 --
      have hc: c ≠ 0 := by
        by_contra! hc
        rw [hc] at h
        simp at h
        have db: b ∣ 83 := by rw [← h]; simp
        rw [Nat.Prime.dvd_iff_eq] at db
        simp [← db] at h
        symm at db
        absurd ne
        simp [hc,db,h]
        norm_num
        by_contra! b_val -- if a = 1 --
        simp [b_val] at h
        simp [hb,b_val,h] at ne
        tauto
      replace ha: 1 ≤ a := by omega
      replace hb: 1 ≤ b := by omega
      replace hc: 1 ≤ c := by omega

      -- Then we show that at least one of them is 1 --
      have l: a < 2 ∨ b < 2 ∨ c < 2 := by
        by_contra! l
        rcases l with ⟨la, lb, lc⟩
        have contra: (a * b + 1) * (b * c + 1) * (c * a + 1)  ≥ 125 := by
          have lab: a * b + 1 ≥ 5 := by nlinarith [la,lb]
          have lbc: b * c + 1 ≥ 5 := by nlinarith [lb,lc]
          have lca: c * a + 1 ≥ 5 := by nlinarith [lc,la]
          calc
            (a * b + 1) * (b * c + 1) * (c * a + 1) ≥ 5 * (b * c + 1) * (c * a + 1) := by nlinarith
                                                  _ ≥  5 * 5 * (c * a + 1) := by nlinarith
                                                  _ ≥  5 * 5 * 5 := by nlinarith
                                                  _ = 125 := by norm_num
        rw [h] at contra
        absurd contra
        norm_num

      -- Now we deal with the cases --
      rcases l with l | l | l

      -- a = 1 --
      . replace l: a = 1 := by omega
        by_cases o: b ≤ c
        -- for b ≤ c --
        . simp [l] at *
          have h1: b ≠ 1 := by -- show that b ≠ 1 --
            by_contra! h1
            simp [h1] at *
            replace h: (c + 1) ^ 2 = 42 := by nlinarith [h]
            have j: c > 5 := by
              by_contra! j
              nlinarith
            have k: c < 6 := by
              by_contra! k
              nlinarith
            nlinarith [j,k]
          have h2: b < 3 := by    -- show that b < 3 --
            by_contra! h2
            replace o: 3 ≤ c := by omega
            have contra: (b + 1) * (b * c + 1) * (c + 1) ≥ 4 * 10 * 4 := by
              have g1: b + 1 ≥ 4 := by nlinarith [h2]
              have g2: b * c + 1 ≥ 10 := by nlinarith [h2,o]
              have g3: c + 1 ≥ 4 := by nlinarith [h2]
              calc
                (b + 1) * (b * c + 1) * (c + 1) ≥ 4 * (b * c + 1) * (c + 1) := by nlinarith
                                                        _ ≥ 4 * 10 * (c + 1) := by nlinarith
                                                        _ ≥ 4 * 10 * 4 := by nlinarith
                                                        _ = 160 := by norm_num
            rw [h] at contra
            absurd contra
            norm_num
          replace h2: b = 2 := by omega -- now  we must have b = 2 --
          simp [h2] at *
          replace h: (2 * c + 1) * (c + 1) = 28 := by nlinarith [h]
          have j: c > 2 := by
            by_contra! j
            nlinarith
          have k: c < 4 := by
            by_contra! k
            nlinarith
          omega
          -- for b > c, similar as above --
        . replace o: c ≤ b := by omega
          simp [l] at *
          have h1: c ≠ 1 := by -- show that c ≠ 1 --
            by_contra! h1
            simp [h1] at *
            replace h: (b + 1) ^ 2 = 42 := by nlinarith [h]
            have j: b > 5 := by
              by_contra! j
              nlinarith
            have k: b < 6 := by
              by_contra! k
              nlinarith
            nlinarith [j,k]
          have h2: c < 3 := by    -- show that c < 3 --
            by_contra! h2
            replace o: 3 ≤ b := by omega
            have contra: (b + 1) * (b * c + 1) * (c + 1) ≥ 4 * 10 * 4 := by
              have g1: c + 1 ≥ 4 := by nlinarith [h2]
              have g2: b * c + 1 ≥ 10 := by nlinarith [h2,o]
              have g3: b + 1 ≥ 4 := by nlinarith [h2]
              calc
                (b + 1) * (b * c + 1) * (c + 1) ≥ 4 * (b * c + 1) * (c + 1) := by nlinarith
                                                        _ ≥ 4 * 10 * (c + 1) := by nlinarith
                                                        _ ≥ 4 * 10 * 4 := by nlinarith
                                                        _ = 160 := by norm_num
            rw [h] at contra
            absurd contra
            norm_num
          replace h2: c = 2 := by omega -- now we must have c = 2 --
          simp [h2] at *
          replace h: (2 * b + 1) * (b + 1) = 28 := by nlinarith [h]
          have j: b > 2 := by
            by_contra! j
            nlinarith
          have k: b < 4 := by
            by_contra! k
            nlinarith
          omega

      -- b = 1 --
      . replace l: b = 1 := by omega
        by_cases o: a ≤ c
        -- for a ≤ c --
        . simp [l] at *
          have h1: a ≠ 1 := by -- show that a ≠ 1 --
            by_contra! h1
            simp [h1] at *
            replace h: (c + 1) ^ 2 = 42 := by nlinarith [h]
            have j: c > 5 := by
              by_contra! j
              nlinarith
            have k: c < 6 := by
              by_contra! k
              nlinarith
            nlinarith [j,k]
          have h2: a < 3 := by    -- show that a < 3 --
            by_contra! h2
            replace o: 3 ≤ c := by omega
            have contra: (a + 1) * (c + 1) * (c * a + 1) ≥ 4 * 4 * 10 := by
              have g1: a + 1 ≥ 4 := by nlinarith [h2]
              have g2: c * a + 1 ≥ 10 := by nlinarith [h2,o]
              have g3: c + 1 ≥ 4 := by nlinarith [o]
              calc
                (a + 1) * (c + 1) * (c * a + 1) ≥ 4 * (c + 1) * (c * a + 1) := by nlinarith
                                                        _ ≥ 4 * 4 * (c + 1) := by nlinarith
                                                        _ ≥ 4 * 4 * 10 := by nlinarith
                                                        _ = 160 := by norm_num
            rw [h] at contra
            absurd contra
            norm_num
          replace h2: a = 2 := by omega -- now  we must have a = 2 --
          simp [h2] at *
          replace h: (2 * c + 1) * (c + 1) = 28 := by nlinarith [h]
          have j: c > 2 := by
            by_contra! j
            nlinarith
          have k: c < 4 := by
            by_contra! k
            nlinarith
          omega
          -- for a > c, similar as above --
        . replace o: c ≤ a := by omega
          simp [l] at *
          have h1: c ≠ 1 := by -- show that c ≠ 1 --
            by_contra! h1
            simp [h1] at *
            replace h: (a + 1) ^ 2 = 42 := by nlinarith [h]
            have j: a > 5 := by
              by_contra! j
              nlinarith
            have k: a < 6 := by
              by_contra! k
              nlinarith
            nlinarith [j,k]
          have h2: c < 3 := by    -- show that c < 3 --
            by_contra! h2
            replace o: 3 ≤ a := by omega
            have contra: (a + 1) * (c + 1) * (c * a + 1) ≥ 4 * 4 * 10 := by
              have g1: a + 1 ≥ 4 := by nlinarith [h2]
              have g2: c * a + 1 ≥ 10 := by nlinarith [h2,o]
              have g3: c + 1 ≥ 4 := by nlinarith [o]
              calc
                (a + 1) * (c + 1) * (c * a + 1) ≥ 4 * (c + 1) * (c * a + 1) := by nlinarith
                                                        _ ≥ 4 * 4 * (c + 1) := by nlinarith
                                                        _ ≥ 4 * 4 * 10 := by nlinarith
                                                        _ = 160 := by norm_num
            rw [h] at contra
            absurd contra
            norm_num
          replace h2: c = 2 := by omega -- now we must have c = 2 --
          simp [h2] at *
          replace h: (2 * a + 1) * (a + 1) = 28 := by nlinarith [h]
          have j: a > 2 := by
            by_contra! j
            nlinarith
          have k: a < 4 := by
            by_contra! k
            nlinarith
          omega

      -- c = 1 --
      . replace l: c = 1 := by omega
        by_cases o: a ≤ b
        -- for a ≤ b --
        . simp [l] at *
          have h1: a ≠ 1 := by -- show that a ≠ 1 --
            by_contra! h1
            simp [h1] at *
            replace h: (b + 1) ^ 2 = 42 := by nlinarith [h]
            have j: b > 5 := by
              by_contra! j
              nlinarith
            have k: b < 6 := by
              by_contra! k
              nlinarith
            nlinarith [j,k]
          have h2: a < 3 := by    -- show that a < 3 --
            by_contra! h2
            replace o: 3 ≤ b := by omega
            have contra: (a * b + 1) * (b + 1) * (a + 1) ≥ 10 * 4 * 4 := by
              have g1: a + 1 ≥ 4 := by nlinarith [h2]
              have g2: a * b + 1 ≥ 10 := by nlinarith [h2,o]
              have g3: b + 1 ≥ 4 := by nlinarith [o]
              calc
                (a * b + 1) * (b + 1) * (a + 1) ≥ 10 * (b + 1) * (a + 1) := by nlinarith
                                                        _ ≥ 10 * 4 * (a + 1) := by nlinarith
                                                        _ ≥ 4 * 4 * 10 := by nlinarith
                                                        _ = 160 := by norm_num
            rw [h] at contra
            absurd contra
            norm_num
          replace h2: a = 2 := by omega -- now  we must have a = 2 --
          simp [h2] at *
          replace h: (2 * b + 1) * (b + 1) = 28 := by nlinarith [h]
          have j: b > 2 := by
            by_contra! j
            nlinarith
          have k: b < 4 := by
            by_contra! k
            nlinarith
          omega
          -- for a > b, similar as above --
        . replace o: b ≤ a := by omega
          simp [l] at *
          have h1: b ≠ 1 := by -- show that b ≠ 1 --
            by_contra! h1
            simp [h1] at *
            replace h: (a + 1) ^ 2 = 42 := by nlinarith [h]
            have j: a > 5 := by
              by_contra! j
              nlinarith
            have k: a < 6 := by
              by_contra! k
              nlinarith
            nlinarith [j,k]
          have h2: b < 3 := by    -- show that b < 3 --
            by_contra! h2
            replace o: 3 ≤ a := by omega
            have contra: (a * b + 1) * (b + 1) * (a + 1) ≥ 10 * 4 * 4 := by
              have g1: a + 1 ≥ 4 := by nlinarith [h2]
              have g2: a * b + 1 ≥ 10 := by nlinarith [h2,o]
              have g3: b + 1 ≥ 4 := by nlinarith [o]
              calc
                (a * b + 1) * (b + 1) * (a + 1) ≥ 10 * (b + 1) * (a + 1) := by nlinarith
                                                        _ ≥ 10 * 4 * (a + 1) := by nlinarith
                                                        _ ≥ 4 * 4 * 10 := by nlinarith
                                                        _ = 160 := by norm_num
            rw [h] at contra
            absurd contra
            norm_num
          replace h2: b = 2 := by omega -- now we must have b = 2 --
          simp [h2] at *
          replace h: (2 * a + 1) * (a + 1) = 28 := by nlinarith [h]
          have j: a > 2 := by
            by_contra! j
            nlinarith
          have k: a < 4 := by
            by_contra! k
            nlinarith
          omega

    -- the backward direction --
    . intro h
      simp at h
      simp
      rcases h with h | h | h | h | h | h | h | h | h | h | h | h
      all_goals simp [h]

-- finally, plug the set_eq into the encard --
  rw [set_eq]
  simp[Set.encard]