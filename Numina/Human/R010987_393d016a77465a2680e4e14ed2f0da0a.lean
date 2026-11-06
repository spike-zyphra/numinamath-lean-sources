import Mathlib

set_option maxHeartbeats 400000
/- A positive integer is written on each of the six faces of a cube.
For each vertex of the cube we compute the product of the numbers on the three adjacent faces.
 The sum of these products is 1001. What is the sum of the six numbers on the faces? -/
theorem number_theory_239374 (a1 a2 b1 b2 c1 c2: ℤ) (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : 0 < b1) (hb2 : 0 < b2)
 (hc1 : 0 < c1) (hc2 : 0 < c2) (h: a1 * b1 * c1 + a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1
 + a1 * b1 * c2 + a2 * b1 * c1 + a1 * b2 * c1 + a2 * b2 * c2 = 1001): a1 + a2 + b1 + b2 + c1 + c2 = 31 := by
    -- a1 and a2 are the numbers on the opposite faces, etc. --
    have id: a1 * b1 * c1 + a1 * b2 * c2 + a2 * b1 * c2 + a2 * b2 * c1
 + a1 * b1 * c2 + a2 * b1 * c1 + a1 * b2 * c1 + a2 * b2 * c2 = (a1 + a2) * (b1 + b2) * (c1 + c2) := by
      ring
    rw [id] at h
    -- note that 1001 = 7 * 11 * 13, hence the set {(a1 + a2), (b1 + b2), (c1 + c2)} is a permutation of {7, 11, 13} --
    clear id
    let x := a1 + a2
    have hx: a1 + a2 = x := by rfl
    have xb: 2 ≤ x := by omega
    let y := b1 + b2
    have hy: b1 + b2 = y := by rfl
    have yb: 2 ≤ y := by omega
    let z := c1 + c2
    have hz: c1 + c2 = z := by rfl
    have zb: 2 ≤ z := by omega
    simp [hx, hy, hz] at h
    rw [show a1 + a2 + b1 + b2 + c1 + c2 = x + y + z by simp [x,y,z]; ring]
    clear_value x y z
    clear hx hy hz ha1 ha2 hb1 hb2 hc1 hc2
    -- 7 ∣ one of x,y,z --
    have d7: 7 ∣ x ∨ 7 ∣ y ∨ 7 ∣ z := by
      have o: 7 ∣ x * y * z := by
        rw [h]; omega
      apply Prime.dvd_or_dvd at o
      rcases o with o | o
      . apply Prime.dvd_or_dvd at o
        rcases o with o | o
        . left; exact o
        . right; left; exact o
        norm_num
      . right
        right
        exact o
      norm_num
    -- 11 ∣ one of x,y,z --
    have d11: 11 ∣ x ∨ 11 ∣ y ∨ 11 ∣ z := by
      have o: 11 ∣ x * y * z := by
        rw [h]; omega
      apply Prime.dvd_or_dvd at o
      rcases o with o | o
      . apply Prime.dvd_or_dvd at o
        rcases o with o | o
        . left; exact o
        . right; left; exact o
        norm_num
      . right
        right
        exact o
      norm_num
    -- 13 ∣ one of x,y,z --
    have d13: 13 ∣ x ∨ 13 ∣ y ∨ 13 ∣ z := by
      have o: 13 ∣ x * y * z := by
        rw [h]; omega
      apply Prime.dvd_or_dvd at o
      rcases o with o | o
      . apply Prime.dvd_or_dvd at o
        rcases o with o | o
        . left; exact o
        . right; left; exact o
        norm_num
      . right
        right
        exact o
      norm_num
    -- for convenience, we use by_contra--
    by_contra! no

    -- we show that ¬ 13 ∣ x --
    have dx: ¬ 13 ∣ x := by
      by_contra! dx
      clear d13
      apply exists_eq_mul_right_of_dvd at dx
      rcases dx with ⟨k,dk⟩
      simp [dk] at h
      have k_pos: 1 ≤ k := by
        omega
      rw [dk] at d11
      rcases d11 with d11 | d11 | d11
      -- 11 ∣ x --
      . replace d11: 11 ∣ k := by
          apply Prime.dvd_or_dvd at d11
          rcases d11 with d11 | d11
          . omega
          . exact d11
          norm_num
        apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * y * z = 7 := by nlinarith
        have l_val: l = 1 := by
          by_contra! ne
          replace ne: 2 ≤ l := by omega
          have contra: 8 ≤ l * y * z := by
            calc
              8 = 2 * (2 * 2) := by norm_num
              _ ≤ l * (2 * 2) := by apply Int.mul_le_mul_of_nonneg_right;omega;omega
              _ = 2 * (l * 2) := by ring
              _ ≤ y * (l * 2) := by apply Int.mul_le_mul_of_nonneg_right;omega;omega
              _ = 2 * (y * l) := by ring
              _ ≤ z * (y * l) := by apply Int.mul_le_mul_of_nonneg_right;omega;nlinarith
              _ = l * y * z := by ring
          rw [dl] at contra
          tauto
        simp [l_val] at h
        replace dl: y * z = 7 := by nlinarith
        have o: 7 ∣ y * z := by omega
        have dd7: 7 ∣ y ∨ 7 ∣ z := by
          apply Prime.dvd_or_dvd at o
          exact o
          norm_num
        rcases dd7 with d7 | d7
        -- 7 ∣ y --
        . apply exists_eq_mul_right_of_dvd at d7
          obtain ⟨m,dm⟩ := d7
          have m_pos: 1 ≤ m := by
            omega
          simp [dm] at h
          replace dm: m * z = 1 := by nlinarith
          absurd dm
          nlinarith
        -- 7 ∣ z --
        . apply exists_eq_mul_right_of_dvd at d7
          obtain ⟨m,dm⟩ := d7
          have m_pos: 1 ≤ m := by
            omega
          simp [dm] at h
          replace dm: m * y = 1 := by nlinarith
          absurd dm
          nlinarith
      -- 11 ∣ y --
      . apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have p:= dl
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * k * z = 7 := by nlinarith
        have o: z ∣ 7 := by
          rw[← dl]
          apply Int.dvd_mul_left
        have oz: z = 1 ∨ z = 7 := by
          replace o: z.natAbs ∣ (7: ℤ).natAbs := by
            rw [Int.natAbs_dvd_natAbs]
            exact o
          rw [Nat.dvd_prime] at o
          norm_cast at o
          rcases o with o | o
          . rw [Int.natAbs_eq_iff] at o
            omega
          . rw [Int.natAbs_eq_iff] at o
            omega
          rw [Nat.prime_iff]
          norm_cast
          rw [← Nat.prime_iff]
          norm_num
        rcases oz with oz | oz
        . omega
        . simp [oz] at dl
          have l_val: l = 1 := by nlinarith
          have k_val: k = 1 := by
            nlinarith
          simp [k_val] at dk
          simp [l_val] at p
          omega
      -- 11 ∣ z --
      . apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have p:= dl
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * k * y = 7 := by nlinarith
        have o: y ∣ 7 := by
          rw[← dl]
          apply Int.dvd_mul_left
        have oz: y = 1 ∨ y = 7 := by
          replace o: y.natAbs ∣ (7: ℤ).natAbs := by
            rw [Int.natAbs_dvd_natAbs]
            exact o
          rw [Nat.dvd_prime] at o
          norm_cast at o
          rcases o with o | o
          . rw [Int.natAbs_eq_iff] at o
            omega
          . rw [Int.natAbs_eq_iff] at o
            omega
          rw [Nat.prime_iff]
          norm_cast
          rw [← Nat.prime_iff]
          norm_num
        rcases oz with oz | oz
        . omega
        . simp [oz] at dl
          have l_val: l = 1 := by nlinarith
          have k_val: k = 1 := by
            nlinarith
          simp [k_val] at dk
          simp [l_val] at p
          omega

    -- we show that ¬ 13 ∣ y --
    have dy: ¬ 13 ∣ y := by
      by_contra! dy
      clear d13
      apply exists_eq_mul_right_of_dvd at dy
      rcases dy with ⟨k,dk⟩
      simp [dk] at h
      have k_pos: 1 ≤ k := by
        omega
      rw [dk] at d11
      rcases d11 with d11 | d11 | d11
      -- 11 ∣ x --
      . apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have p:= dl
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * k * z = 7 := by nlinarith
        have o: z ∣ 7 := by
          rw[← dl]
          apply Int.dvd_mul_left
        have oz: z = 1 ∨ z = 7 := by
          replace o: z.natAbs ∣ (7: ℤ).natAbs := by
            rw [Int.natAbs_dvd_natAbs]
            exact o
          rw [Nat.dvd_prime] at o
          norm_cast at o
          rcases o with o | o
          . rw [Int.natAbs_eq_iff] at o
            omega
          . rw [Int.natAbs_eq_iff] at o
            omega
          rw [Nat.prime_iff]
          norm_cast
          rw [← Nat.prime_iff]
          norm_num
        rcases oz with oz | oz
        . omega
        . simp [oz] at dl
          have l_val: l = 1 := by nlinarith
          have k_val: k = 1 := by
            nlinarith
          simp [k_val] at dk
          simp [l_val] at p
          omega
      -- 11 ∣ y --
      . replace d11: 11 ∣ k := by
          apply Prime.dvd_or_dvd at d11
          rcases d11 with d11 | d11
          . omega
          . exact d11
          norm_num
        apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * x * z = 7 := by nlinarith
        have l_val: l = 1 := by
          by_contra! ne
          replace ne: 2 ≤ l := by omega
          have contra: 8 ≤ l * x * z := by
            calc
              8 = 2 * (2 * 2) := by norm_num
              _ ≤ l * (2 * 2) := by apply Int.mul_le_mul_of_nonneg_right;omega;omega
              _ = 2 * (l * 2) := by ring
              _ ≤ x * (l * 2) := by apply Int.mul_le_mul_of_nonneg_right;omega;omega
              _ = 2 * (x * l) := by ring
              _ ≤ z * (x * l) := by apply Int.mul_le_mul_of_nonneg_right;omega;nlinarith
              _ = l * x * z := by ring
          rw [dl] at contra
          tauto
        simp [l_val] at h
        replace dl: x * z = 7 := by nlinarith
        have o: 7 ∣ x * z := by omega
        have dd7: 7 ∣ x ∨ 7 ∣ z := by
          apply Prime.dvd_or_dvd at o
          exact o
          norm_num
        rcases dd7 with d7 | d7
        -- 7 ∣ x --
        . apply exists_eq_mul_right_of_dvd at d7
          obtain ⟨m,dm⟩ := d7
          have m_pos: 1 ≤ m := by
            omega
          simp [dm] at h
          replace dm: m * z = 1 := by nlinarith
          absurd dm
          nlinarith
        -- 7 ∣ z --
        . apply exists_eq_mul_right_of_dvd at d7
          obtain ⟨m,dm⟩ := d7
          have m_pos: 1 ≤ m := by
            omega
          simp [dm] at h
          replace dm: m * x = 1 := by nlinarith
          absurd dm
          nlinarith

      -- 11 ∣ z --
      . apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have p:= dl
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * k * x = 7 := by nlinarith
        have o: x ∣ 7 := by
          rw[← dl]
          apply Int.dvd_mul_left
        have oz: x = 1 ∨ x = 7 := by
          replace o: x.natAbs ∣ (7: ℤ).natAbs := by
            rw [Int.natAbs_dvd_natAbs]
            exact o
          rw [Nat.dvd_prime] at o
          norm_cast at o
          rcases o with o | o
          . rw [Int.natAbs_eq_iff] at o
            omega
          . rw [Int.natAbs_eq_iff] at o
            omega
          rw [Nat.prime_iff]
          norm_cast
          rw [← Nat.prime_iff]
          norm_num
        rcases oz with oz | oz
        . omega
        . simp [oz] at dl
          have l_val: l = 1 := by nlinarith
          have k_val: k = 1 := by
            nlinarith
          simp [k_val] at dk
          simp [l_val] at p
          omega


    -- we show that ¬ 13 ∣ z --
    have dz: ¬ 13 ∣ z := by
      by_contra! dz
      clear d13
      apply exists_eq_mul_right_of_dvd at dz
      rcases dz with ⟨k,dk⟩
      simp [dk] at h
      have k_pos: 1 ≤ k := by
        omega
      rw [dk] at d11
      rcases d11 with d11 | d11 | d11
      -- 11 ∣ x --
      . apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have p:= dl
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * k * y = 7 := by nlinarith
        have o: y ∣ 7 := by
          rw[← dl]
          apply Int.dvd_mul_left
        have oz: y = 1 ∨ y = 7 := by
          replace o: y.natAbs ∣ (7: ℤ).natAbs := by
            rw [Int.natAbs_dvd_natAbs]
            exact o
          rw [Nat.dvd_prime] at o
          norm_cast at o
          rcases o with o | o
          . rw [Int.natAbs_eq_iff] at o
            omega
          . rw [Int.natAbs_eq_iff] at o
            omega
          rw [Nat.prime_iff]
          norm_cast
          rw [← Nat.prime_iff]
          norm_num
        rcases oz with oz | oz
        . omega
        . simp [oz] at dl
          have l_val: l = 1 := by nlinarith
          have k_val: k = 1 := by
            nlinarith
          simp [k_val] at dk
          simp [l_val] at p
          omega
      -- 11 ∣ y --
      . apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have p:= dl
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * k * x = 7 := by nlinarith
        have o: x ∣ 7 := by
          rw[← dl]
          apply Int.dvd_mul_left
        have oz: x = 1 ∨ x = 7 := by
          replace o: x.natAbs ∣ (7: ℤ).natAbs := by
            rw [Int.natAbs_dvd_natAbs]
            exact o
          rw [Nat.dvd_prime] at o
          norm_cast at o
          rcases o with o | o
          . rw [Int.natAbs_eq_iff] at o
            omega
          . rw [Int.natAbs_eq_iff] at o
            omega
          rw [Nat.prime_iff]
          norm_cast
          rw [← Nat.prime_iff]
          norm_num
        rcases oz with oz | oz
        . omega
        . simp [oz] at dl
          have l_val: l = 1 := by nlinarith
          have k_val: k = 1 := by
            nlinarith
          simp [k_val] at dk
          simp [l_val] at p
          omega
      -- 11 ∣ z --
      . replace d11: 11 ∣ k := by
          apply Prime.dvd_or_dvd at d11
          rcases d11 with d11 | d11
          . omega
          . exact d11
          norm_num
        apply exists_eq_mul_right_of_dvd at d11
        obtain ⟨l,dl⟩ := d11
        have l_pos: 1 ≤ l := by
          omega
        simp [dl] at h
        replace dl: l * x * y = 7 := by nlinarith
        have l_val: l = 1 := by
          by_contra! ne
          replace ne: 2 ≤ l := by omega
          have contra: 8 ≤ l * x * y := by
            calc
              8 = 2 * (2 * 2) := by norm_num
              _ ≤ l * (2 * 2) := by apply Int.mul_le_mul_of_nonneg_right;omega;omega
              _ = 2 * (l * 2) := by ring
              _ ≤ x * (l * 2) := by apply Int.mul_le_mul_of_nonneg_right;omega;omega
              _ = 2 * (x * l) := by ring
              _ ≤ y * (x * l) := by apply Int.mul_le_mul_of_nonneg_right;omega;nlinarith
              _ = l * x * y := by ring
          rw [dl] at contra
          tauto
        simp [l_val] at h
        replace dl: x * y = 7 := by nlinarith
        have o: 7 ∣ x * y := by omega
        have dd7: 7 ∣ x ∨ 7 ∣ y := by
          apply Prime.dvd_or_dvd at o
          exact o
          norm_num
        rcases dd7 with d7 | d7
        -- 7 ∣ x --
        . apply exists_eq_mul_right_of_dvd at d7
          obtain ⟨m,dm⟩ := d7
          have m_pos: 1 ≤ m := by
            omega
          simp [dm] at h
          replace dm: m * y = 1 := by nlinarith
          absurd dm
          nlinarith
        -- 7 ∣ y --
        . apply exists_eq_mul_right_of_dvd at d7
          obtain ⟨m,dm⟩ := d7
          have m_pos: 1 ≤ m := by
            omega
          simp [dm] at h
          replace dm: m * x = 1 := by nlinarith
          absurd dm
          nlinarith
    -- Finally, we use d13 to arrive at a contradiction --
    tauto