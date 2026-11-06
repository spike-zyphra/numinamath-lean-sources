import Mathlib

set_option maxHeartbeats 400000
/- find all triples (p,x,y) such that p ^ x = y ^ 4 + 4, where p is prime, and x, y are natural numbers -/
theorem number_theory_607834: {(p, x, y) : ℕ × ℕ × ℕ | Nat.Prime p ∧  p ^ x = y ^ 4 + 4} = {(5, 1, 1),(2, 2, 0)} := by
  ext ⟨p,x,y⟩
  constructor

  -- the forward direction --
  . intro h
    simp at h
    rcases h with ⟨hp, h⟩
    simp
    by_cases hy: y < 2
    -- firstly tackle the case y = 0,1 --
    . replace hy: y = 0 ∨ y = 1 := by omega
      rcases hy with hy | hy
      -- case y = 0 --
      . simp [hy] at h
        right
        simp [hy]
        have l: p < 3 := by
          by_contra! l
          have o: x < 2 := by
            by_contra! o
            have contra: p ^ x ≥ 9 := by
              calc
                p ^ x ≥ 3 ^ x := by simp; apply Nat.pow_le_pow_left; exact l
                    _ ≥ 3 ^ 2 := by simp; rw [show 9 = 3 ^ 2 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                    _ = 9 := by simp
            rw [h] at contra
            tauto
          replace o: x = 0 ∨ x = 1 := by omega
          rcases o with o | o
          . simp [o] at h
          . simp [o] at h
            rw [h] at hp
            absurd hp
            norm_num
        have p_val: p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases p_val with p_val | p_val | p_val
        . rw [p_val] at hp
          absurd hp
          norm_num
        . rw [p_val] at hp
          absurd hp
          norm_num
        . simp [p_val] at h
          simp [p_val]
          have j: x < 3 := by
            by_contra! j
            have contra: 2 ^ x ≥ 8 := by
              calc
                2 ^ x ≥ 2 ^ 3 := by simp; rw [show 8 = 2 ^ 3 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                    _ = 8 := by simp
            rw [h] at contra
            tauto
          have k: x > 1 := by
            by_contra! k
            have contra: 2 ^ x ≤ 2 := by
              calc
                2 ^ x ≤ 2 ^ 1 := by simp; rw [show 2 = 2 ^ 1 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                    _ = 2 := by simp
            rw [h] at contra
            tauto
          omega
        -- case y = 1 --
      . simp [hy] at h
        left
        simp [hy]
        by_contra! no
        have l: p < 3 := by
          by_contra! l
          have o: x < 2 := by
            by_contra! o
            have contra: p ^ x ≥ 9 := by
              calc
                p ^ x ≥ 3 ^ x := by simp; apply Nat.pow_le_pow_left; exact l
                    _ ≥ 3 ^ 2 := by simp; rw [show 9 = 3 ^ 2 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                    _ = 9 := by simp
            rw [h] at contra
            tauto
          replace o: x = 0 ∨ x = 1 := by omega
          rcases o with o | o
          . simp [o] at h
          . simp [o] at h
            rw [h] at hp
            simp [h] at no
            tauto
        have p_val: p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases p_val with p_val | p_val | p_val
        . rw [p_val] at hp
          absurd hp
          norm_num
        . rw [p_val] at hp
          absurd hp
          norm_num
        . simp [p_val] at h
          have j: x < 3 := by
            by_contra! j
            have contra: 2 ^ x ≥ 8 := by
              calc
                2 ^ x ≥ 2 ^ 3 := by simp; rw [show 8 = 2 ^ 3 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                    _ = 8 := by simp
            rw [h] at contra
            tauto
          have k: x > 1 := by
            by_contra! k
            have contra: 2 ^ x ≤ 2 := by
              calc
                2 ^ x ≤ 2 ^ 1 := by simp; rw [show 2 = 2 ^ 1 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                    _ = 2 := by simp
            rw [h] at contra
            tauto
          replace k: x = 2 := by omega
          simp [k] at h

    -- now consider the case y ≥ 2, then y ^ 2 - 2 * y ≥ 0 --
    . have H:= h
      simp at hy
      have hy1: 0 ≤ y ^ 2 - 2 * y := by nlinarith
      have hp2: 2 ≤ p := by
        by_contra! hp2
        absurd hp
        replace hp2 : p = 0 ∨ p = 1 := by omega
        rcases hp2 with hp2 | hp2
        . rw [hp2]
          norm_num
        . rw [hp2]
          norm_num
      have id: y ^ 4 + 4 = (y ^ 2 - 2 * y + 2) * (y ^ 2 + 2 * y + 2) := by
         zify  --use the "zify" trick--
         have w: Nat.cast (y ^ 2 - 2 * y) = (y: ℤ) ^ 2 - 2 * ↑y := by
            rw [Int.natCast_sub]
            simp
            nlinarith
         rw [w]
         ring
      rw [id] at h
      have dvd1: (y ^ 2 - 2 * y + 2) ∣ p ^ x := by rw [h]; apply Nat.dvd_mul_right
      have dvd2: (y ^ 2 + 2 * y + 2) ∣ p ^ x := by rw [h]; apply Nat.dvd_mul_left
      rw [Nat.dvd_prime_pow] at dvd1
      rw [Nat.dvd_prime_pow] at dvd2
      obtain ⟨m,hm,h1⟩ := dvd1
      obtain ⟨n,hn,h2⟩ := dvd2  -- now we can write y ^ 2 - 2 * y + 2 = p ^ m and y ^ 2 + 2 * y + 2 = p ^ n --
      simp [h1,h2] at h
      replace h: m + n = x := by -- hence m + n = x --
        rw [show p ^ m * p ^ n = p ^ (m + n) by rw[← Nat.pow_add]] at h
        have l1: m + n ≤ x := by
          replace h: p ^ (m + n) ≤ p ^ x := by omega
          rw [Nat.pow_le_pow_iff_right] at h
          exact h
          omega
        have l2: x ≤ m + n := by
          replace h: p ^ x ≤ p ^ (m + n) := by omega
          rw [Nat.pow_le_pow_iff_right] at h
          exact h
          omega
        omega
      clear id
      have hm2: 1 ≤ m := by
        by_contra! no
        replace no: m = 0 := by omega
        simp [no] at h1
      have hn2: 1 ≤ n := by
        by_contra! no
        replace no: n = 0 := by omega
        simp [no] at h2
      have h1p: p ∣ (y ^ 2 - 2 * y + 2) := by
        rw [h1]
        apply dvd_pow_self
        omega
      have h2p: p ∣ (y ^ 2 + 2 * y + 2) := by
        rw [h2]
        apply dvd_pow_self
        omega
      have dvd: p ∣ 4 * y := by   -- key dvd relation --
        have eq: 4 * y = (y ^ 2 + 2 * y + 2) - (y ^ 2 - 2 * y + 2) := by
        -- it's not easy to prove this in ℕ --
          let g:= y ^ 2 + 2
          have hg: y ^ 2 + 2 = g := by rfl
          let f:= 2 * y
          have hf: 2 * y = f := by rfl
          have eq1: y ^ 2 + 2 * y + 2 = g + 2 * y := by
            simp [g]
            abel
          have eq2: y ^ 2 - 2 * y + 2 = g - 2 * y:= by
            simp [g]
            symm
            apply Nat.sub_add_comm
            nlinarith
          rw [eq1,eq2]
          rw [show 4 * y = 2 * (2 * y) by ring]
          simp [hf]
          rw [Nat.add_sub_sub_cancel]
          ring
          simp [f,g]
          nlinarith

        rw [eq]
        apply Nat.dvd_sub
        simp
        nlinarith
        exact h2p
        exact h1p
      replace dvd: p ∣ 4 ∨ p ∣ y := by
        rw [Nat.Prime.dvd_mul] at dvd
        exact dvd
        exact hp
      rcases dvd with dvd | dvd
      -- case p ∣ 4 --
      . have dvd2:= dvd
        apply Nat.le_of_dvd at dvd
        have p_val: p = 2 ∨ p = 3 ∨ p = 4 := by omega
        rcases p_val with p_val | p_val | p_val
        -- cases p = 2 --
        . simp [p_val] at *
          clear dvd2 h2 h2p hy1 hp2 hp hm h hm2
          have i: 2 ∣ (y ^ 4 + 4) := by    -- we show 2 ∣ y --
            rw [← H]
            apply dvd_pow_self
            omega
          replace i: 2 ∣ y ^ 4 := by omega
          replace i: 2 ∣ y := by
            apply Nat.Prime.dvd_of_dvd_pow at i
            exact i
            norm_num
          apply exists_eq_mul_right_of_dvd at i
          obtain ⟨z,hz⟩ := i
          rw [hz] at H
          by_cases z_val: z = 0
          -- case z = 0 --
          . simp [z_val] at H
            have j: x < 3 := by
              by_contra! j
              have contra: 2 ^ x ≥ 8 := by
                calc
                  2 ^ x ≥ 2 ^ 3 := by simp; rw [show 8 = 2 ^ 3 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                      _ = 8 := by simp
              rw [H] at contra
              tauto
            have k: x > 1 := by
              by_contra! k
              have contra: 2 ^ x ≤ 2 := by
                calc
                  2 ^ x ≤ 2 ^ 1 := by simp; rw [show 2 = 2 ^ 1 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                      _ = 2 := by simp
              rw [H] at contra
              tauto
            have o: x = 2 := by omega
            simp [z_val] at hz
            omega
          -- case z ≥ 1 --
          have t: 8 ∣ (2 * z) ^ 4 := by
            have eq: (2 * z) ^ 4 = 8 * (2 * z ^ 4) := by
              calc
                (2 * z) ^ 4 = 2 ^ 4 * z ^ 4 := by nlinarith
                         _ = 16 * (z ^ 4):= by norm_num
                         _ = 8 * (2 * z ^ 4) := by nlinarith
            rw [eq]
            apply Nat.dvd_mul_right
          have bx: x < 3 := by
            by_contra! bx
            have dx: 8 ∣ 2 ^ x := by
              rw [show 8 = 2 ^ 3 by omega]
              apply Nat.pow_dvd_pow
              exact bx
            have contra: 8 ∣ 4 := by
              have eq: 4 = 2 ^ x - (2 * z) ^ 4 := by omega
              rw [eq]
              apply Nat.dvd_sub
              nlinarith
              exact dx
              exact t
            tauto
          have x_val: x = 1 ∨ x = 2 := by omega
          rcases x_val with x_val | x_val
          . simp [x_val] at H
          . simp [x_val] at H
            simp [H] at hz
            omega
        -- cases p = 3 and p = 4 --
        . rw [p_val] at dvd2
          tauto
        . rw [p_val] at hp
          tauto
        omega
      -- case p ∣ y, we show that p = 2 indeed--
      . have o: p ∣ y ^ 2 + 2 * y := by
          rw [show y ^ 2 + 2 * y = y * (y + 2) by ring]
          have j: y ∣ y * (y + 2) := by
            apply Nat.dvd_mul_right
          apply Nat.dvd_trans dvd j
        replace o: p ∣ 2 := by
          have eq: 2 = (y ^ 2 + 2 * y + 2) - (y ^ 2 + 2 * y) := by symm; apply Nat.add_sub_cancel_left
          rw [eq]
          apply Nat.dvd_sub
          simp
          exact h2p
          exact o
        apply Nat.le_of_dvd at o
        replace o: p = 2 := by omega -- now p = 2, returns to the case before --
        simp [o] at *
        clear h2 h2p hy1 hp2 hp h h1
        have i: 2 ∣ (y ^ 4 + 4) := by    -- we show 2 ∣ y --
          rw [← H]
          apply dvd_pow_self
          omega
        replace i: 2 ∣ y ^ 4 := by omega
        replace i: 2 ∣ y := by
          apply Nat.Prime.dvd_of_dvd_pow at i
          exact i
          norm_num
        apply exists_eq_mul_right_of_dvd at i
        obtain ⟨z,hz⟩ := i
        rw [hz] at H
        by_cases z_val: z = 0
        -- case z = 0 --
        . simp [z_val] at H
          have j: x < 3 := by
            by_contra! j
            have contra: 2 ^ x ≥ 8 := by
              calc
                  2 ^ x ≥ 2 ^ 3 := by simp; rw [show 8 = 2 ^ 3 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                      _ = 8 := by simp
            rw [H] at contra
            tauto
          have k: x > 1 := by
            by_contra! k
            have contra: 2 ^ x ≤ 2 := by
              calc
                  2 ^ x ≤ 2 ^ 1 := by simp; rw [show 2 = 2 ^ 1 by omega]; apply Nat.pow_le_pow_of_le_right; omega;omega
                      _ = 2 := by simp
            rw [H] at contra
            tauto
          have o: x = 2 := by omega
          simp [z_val] at hz
          omega
        -- case z ≥ 1 --
        . have t: 8 ∣ (2 * z) ^ 4 := by
            have eq: (2 * z) ^ 4 = 8 * (2 * z ^ 4) := by
              calc
                  (2 * z) ^ 4 = 2 ^ 4 * z ^ 4 := by nlinarith
                          _ = 16 * (z ^ 4):= by norm_num
                          _ = 8 * (2 * z ^ 4) := by nlinarith
            rw [eq]
            apply Nat.dvd_mul_right
          have bx: x < 3 := by
            by_contra! bx
            have dx: 8 ∣ 2 ^ x := by
              rw [show 8 = 2 ^ 3 by omega]
              apply Nat.pow_dvd_pow
              exact bx
            have contra: 8 ∣ 4 := by
              have eq: 4 = 2 ^ x - (2 * z) ^ 4 := by omega
              rw [eq]
              apply Nat.dvd_sub
              nlinarith
              exact dx
              exact t
            tauto
          have x_val: x = 1 ∨ x = 2 := by omega
          rcases x_val with x_val | x_val
          . simp [x_val] at H
          . simp [x_val] at H
            simp [H] at hz
            omega

        omega
      exact hp
      exact hp

  -- the backward direction --
  . intro h
    simp at h
    simp
    rcases h with h | h
    . simp [h]
      norm_num
    . simp [h]
      norm_num