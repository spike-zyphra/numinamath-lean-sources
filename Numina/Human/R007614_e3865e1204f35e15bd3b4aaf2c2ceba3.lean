import Mathlib

/- Find all triples of integers $(a, b, c)$ such that the number

$$
N=\frac{(a-b)(b-c)(c-a)}{2}+2
$$

is a power of 2016 . -/
theorem number_theory_605357: {(a, b, c): ℤ × ℤ × ℤ | ∃ z: ℕ, (a - b) * (b - c) * (c - a) / (2: ℚ) + 2 = 2016 ^ z}
 = {(a, b, c): ℤ × ℤ × ℤ | (∃ k: ℤ, a = k + 2 ∧ b = k + 1 ∧ c = k) ∨ (∃ k: ℤ, a = k + 1 ∧ b = k ∧ c = k + 2) ∨
 (∃ k: ℤ, a = k ∧ b = k + 2 ∧ c = k + 1)} := by
  ext ⟨a,b,c⟩
  simp only [Set.mem_setOf_eq]
  constructor
  -- the forward direction
  . intro h
    obtain ⟨z, h⟩ := h
    replace h: (↑a - ↑b) * (↑b - ↑c) * (↑c - ↑a) + (4: ℚ) = 2 * 2016 ^ z := by linarith
    norm_cast at h
    simp at h
    set x:= b - a with hx
    set y:= c - b with hy
    replace hx: a - b = -x := by simp [hx]
    replace hy: b - c = -y := by simp [hy]
    have hl: c - a = x + y := by linarith
    simp [hx,hy,hl] at h
    by_cases hz: 1 ≤ z
    -- case: 1 ≤ z, we show contradiction by mod 7
    . have d7: (7: ℤ) ∣ 2 * 2016 ^ z := by
        set u:= z - 1 with hu
        replace hu: z = u + 1 := by simp [hu]; omega
        have eq: 2016 ^ z = (2016: ℤ) * 2016 ^ u := by
          simp [hu];omega
        rw [eq]
        rw [show (2: ℤ) * (2016 * 2016 ^ u) = 2016 * (2 * 2016 ^ u) by ring]
        have o: (7: ℤ) ∣ 2016 := by
          norm_num
        have o1: (2016: ℤ) ∣ 2016 * (2 * 2016 ^ u) := by
          apply dvd_mul_right
        apply dvd_trans o o1
      rw [← h] at d7
      clear h
      have contra: ((x + y) ^ 3 - x ^ 3 - y ^ 3) % 7 = 2 := by   -- this is where we get the contradiction
        have o1: 7 ∣ (x + y) ^ 3 - x ^ 3 - y ^ 3 + 12 := by
          have eq: (x + y) ^ 3 - x ^ 3 - y ^ 3 + 12 = 3 * (x * y * (x + y) + 4) := by ring
          rw [eq]
          have o2: (x * y * (x + y) + 4) ∣ 3 * (x * y * (x + y) + 4) := by
            apply dvd_mul_left
          apply dvd_trans d7 o2
        apply Int.emod_eq_zero_of_dvd at o1
        have modeq: (((x + y) ^ 3 - x ^ 3 - y ^ 3) % 7 + 12 % 7) % 7 = ((x + y) ^ 3 - x ^ 3 - y ^ 3 + 12) % 7 := by
          rw [← Int.add_emod]
        rw [o1] at modeq
        omega
      set r:= x % 7 with hr
      set s:= y % 7 with hs
      replace hr: x % 7 = r := by simp [r]
      replace hs: y % 7 = s := by simp [s]
      have hr1: 0 ≤ r := by omega
      have hr2: r < 7 := by omega
      have hs1: 0 ≤ s := by omega
      have hs2: s < 7 := by omega
      rw [Int.sub_emod] at contra
      rw [show ((x + y) ^ 3 - x ^ 3) % 7 = ((x + y) ^ 3 % 7 - x ^ 3 % 7) % 7 by simp [Int.sub_emod]] at contra
      have k1: (x + y) ^ 3 % 7 = (r + s) ^ 3 % 7 := by
        rw [show (x + y) ^ 3 = (x + y) * (x + y) * (x + y) by ring]
        simp [Int.mul_emod]
        rw [Int.add_emod]
        rw [hr,hs]
        simp
        simp [← Int.mul_emod]
        ring_nf
      have k2: x ^ 3 % 7 = r ^ 3 % 7 := by
        rw [show x ^ 3 = x * x * x by ring]
        simp [Int.mul_emod]
        rw [hr]
        simp
        simp [← Int.mul_emod]
        ring_nf
      have k3: y ^ 3 % 7 = s ^ 3 % 7 := by
        rw [show y ^ 3 = y * y * y by ring]
        simp [Int.mul_emod]
        rw [hs]
        simp
        simp [← Int.mul_emod]
        ring_nf
      simp [k1,k2,k3] at contra
      absurd contra
      clear * - hr1 hr2 hs1 hs2  -- we enumarate all the cases by mod7
      interval_cases r <;> interval_cases s <;> omega
    -- case: z = 0
    . simp at hz
      simp [hz] at h
      clear hz
      replace h: x * y * (x + y) = -2 := by linarith
      have v: x = -1 ∧ y = -1 ∨ x = 2 ∧ y = -1 ∨ x = -1 ∧ y = 2 := by --we see that thare are only 3 cases
        have dx: x ∣ -2 := by
          rw [← h]
          rw [show x * y * (x + y) = x * (y * (x + y)) by ring]
          apply dvd_mul_right
        rw [← Int.natAbs_dvd_natAbs] at dx
        simp at dx
        apply Nat.le_of_dvd at dx
        have dy: y ∣ -2 := by
          rw [← h]
          rw [show x * y * (x + y) = y * (x * (x + y)) by ring]
          apply dvd_mul_right
        rw [← Int.natAbs_dvd_natAbs] at dy
        simp at dy
        apply Nat.le_of_dvd at dy
        zify at dx dy
        rw [show x = x - 0 by ring] at dx
        rw [show y = y - 0 by ring] at dy
        rw [abs_sub_le_iff] at dx dy
        simp at dx dy
        rcases dx with ⟨dx1, dx2⟩
        replace dx2: -2 ≤ x := by linarith
        rcases dy with ⟨dy1, dy2⟩
        replace dy2: -2 ≤ y := by linarith
        interval_cases x <;> interval_cases y <;> omega
        all_goals norm_num
      rcases v with v | v | v
      -- cases: x = -1, y = -1
      . left
        use c
        omega
      -- cases: x = 2, y = -1
      . right
        right
        use a
        omega
      -- cases: x = -1, y = 2
      . right
        left
        use b
        omega

  -- the backward direction
  . intro h
    rcases h with h | h | h
    all_goals obtain ⟨k, hk⟩:= h
    all_goals simp [hk]; use 0; norm_num