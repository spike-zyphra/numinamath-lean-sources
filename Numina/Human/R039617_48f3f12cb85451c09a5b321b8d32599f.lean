import Mathlib

set_option maxHeartbeats 400000

/-Suppose a and b are positive integers for which
8 * a ^ a * b ^ b = 27 * a ^ b * b ^ a. Find a ^ 2 + b ^ 2-/

theorem algebra_610337 {a b: ℕ} (ha: 0 < a) (hb: 0 < b) (h: 8 * a ^ a * b ^ b = 27 * a ^ b * b ^ a):
  a ^ 2 + b ^ 2 = 117 := by

  -- we first show that a ≠ b
  have o: a ≠ b := by
    by_contra! o
    simp [o] at h

  -- then we write a and b in terms of gcd
  let d := Nat.gcd a b
  let x := a / d
  let y := b / d
  have dx: d ∣ a := by
    apply Nat.gcd_dvd_left
  have dy: d ∣ b := by
    apply Nat.gcd_dvd_right
  have hx: a = d * x := by
    simp [x]
    symm
    apply Nat.mul_div_cancel'
    exact dx
  have hy: b = d * y := by
    simp [y]
    symm
    apply Nat.mul_div_cancel'
    exact dy
  have pp: Nat.Coprime x y := by
    simp [x, y]
    apply Nat.coprime_div_gcd_div_gcd
    apply Nat.gcd_pos_of_pos_left
    exact ha
  replace o: x ≠ y := by
    simp [x, y]
    by_contra! o
    field_simp at o
    tauto

  -- then we prove by two cases
  by_cases l: x < y
  -- case1: x < y
  .
    -- we simply h firstly

    have l': a < b := by
      simp [hx, hy]
      nlinarith
    have eq1: 8 * a ^ a * b ^ b = (a ^ a * b ^ a) * (8 * b ^ (b - a)) := by
      have o1: b ^ b = b ^ a * b ^ (b - a) := by
        nth_rewrite 2 [show b = b - a + a by omega]
        rw [Nat.pow_add]
        ring
      rw [o1]
      ring
    rw [eq1] at h
    clear eq1
    have eq2: 27 * a ^ b * b ^ a = (a ^ a * b ^ a) * (27 * a ^ (b - a)) := by
      have o1: a ^ b = a ^ a * a ^ (b - a) := by
        nth_rewrite 1 [show b = b - a + a by omega]
        rw [Nat.pow_add]
        ring
      rw [o1]
      ring
    rw [eq2] at h
    clear eq2
    have hp: 0 < a ^ a * b ^ a := by
      have o1: 0 < a ^ a := by
        apply Nat.pow_pos
        exact ha
      have o2: 0 < b ^ a := by
        apply Nat.pow_pos
        exact hb
      nlinarith
    apply Nat.mul_left_cancel hp at h
    clear hp
    have eq1: 8 * b ^ (b - a) = d ^ (d * y - d * x) * (8 * y ^ (d * y - d * x)) := by
      simp [hx, hy]
      ring
    have eq2: 27 * a ^ (b - a) = d ^ (d * y - d * x) * (27 * x ^ (d * y - d * x)) := by
      simp [hx, hy]
      ring
    rw [eq1, eq2] at h
    clear eq1 eq2
    have hp: 0 < d ^ (d * y - d * x) := by
        apply Nat.pow_pos
        by_contra! o
        replace o: d = 0 := by omega
        simp [o] at dx
        omega
    apply Nat.mul_left_cancel hp at h
    clear hp
    set i:= d * y - d * x with hi
    have oi: 0 < i := by
          simp [i]
          omega

    -- then we have y ∣ 27, hence y = 3 ^ m
    have uy: ∃ m, y = 3 ^ m := by
      have oy: y ∣ 27 := by
        have o1: y ∣ 8 * y ^ i := by
          have eq: y ^ i = y ^ (i - 1) * y := by
            nth_rewrite 1 [show i = i - 1 + 1 by omega]
            ring
          rw [eq]
          rw [show 8 * (y ^ (i - 1) * y) = 8 * y ^ (i - 1) * y by ring]
          simp
        rw [h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        apply Nat.Coprime.symm
        exact pp
      replace oy: y ∈ Nat.divisors 27 := by
        simp
        exact oy
      have eq: Nat.divisors 27 = {1, 3, 9, 27} := by
        native_decide
      rw [eq] at oy
      clear eq
      simp at oy
      rcases oy with u | u | u | u
      .
        use 0
        simp [u]
      .
        use 1
        simp [u]
      .
        use 2
        simp [u]
      .
        use 3
        simp [u]
    obtain ⟨m, hm⟩ := uy

    -- similar for x
    have ux: ∃ n, x = 2 ^ n := by
      have ox: x ∣ 8 := by
        have o1: x ∣ 27 * x ^ i := by
          have eq: x ^ i = x ^ (i - 1) * x := by
            nth_rewrite 1 [show i = i - 1 + 1 by omega]
            ring
          rw [eq]
          rw [show 27 * (x ^ (i - 1) * x) = 27 * x ^ (i - 1) * x by ring]
          simp
        rw [← h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        exact pp
      replace ox: x ∈ Nat.divisors 8 := by
        simp
        exact ox
      have eq: Nat.divisors 8 = {1, 2, 4, 8} := by
        native_decide
      rw [eq] at ox
      clear eq
      simp at ox
      rcases ox with u | u | u | u
      .
        use 0
        simp [u]
      .
        use 1
        simp [u]
      .
        use 2
        simp [u]
      .
        use 3
        simp [u]
    obtain ⟨n, hn⟩ := ux

    -- then we show that mi = ni = 3
    simp [hm, hn] at h
    rw [show (3 ^ m) ^ i = 3 ^ (m * i) by rw [← Nat.pow_mul]] at h
    rw [show (2 ^ n) ^ i = 2 ^ (n * i) by rw [← Nat.pow_mul]] at h
    have rm: m * i = 3 := by
      have l1: 27 ∣ 3 ^ (m * i) := by
        have o1: 27 ∣ 27 * 2 ^ (n * i) := by
          simp
        rw [← h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_left at o1
        exact o1
        norm_num
      have l2: 3 ^ (m * i) ∣ 27 := by
        have o1: 3 ^ (m * i) ∣ 8 * 3 ^ (m * i) := by
          simp
        rw [h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        apply Nat.Coprime.pow_left
        norm_num
      have r1: 3 ^ (m * i) = 27 := by
        apply Nat.dvd_antisymm
        exact l2
        exact l1
      rw [show 27 = 3 ^ 3 by norm_num] at r1
      rw [pow_right_inj₀] at r1
      exact r1
      norm_num
      norm_num

    -- similar for n
    have rn: n * i = 3 := by
      have l1: 8 ∣ 2 ^ (n * i) := by
        have o1: 8 ∣ 8 * 3 ^ (m * i) := by
          simp
        rw [h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_left at o1
        exact o1
        norm_num
      have l2: 2 ^ (n * i) ∣ 8 := by
        have o1: 2 ^ (n * i) ∣ 27 * 2 ^ (n * i) := by
          simp
        rw [← h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        apply Nat.Coprime.pow_left
        norm_num
      have r1: 2 ^ (n * i) = 8 := by
        apply Nat.dvd_antisymm
        exact l2
        exact l1
      rw [show 8 = 2 ^ 3 by norm_num] at r1
      rw [pow_right_inj₀] at r1
      exact r1
      norm_num
      norm_num

    -- then we can check all finite cases
    have s: m = n := by
      rw [← rn] at rm
      nlinarith
    have en: n ∣ 3 := by
      rw [← rn]
      simp
    apply Nat.le_of_dvd at en
    simp [s] at hm
    simp [hm, hn] at hi
    simp [hi] at rn
    interval_cases n
    .
      simp at rn
    .
      simp at rn
      replace rn: d = 3 := by omega
      simp [hm, hn, rn] at hx hy
      simp [hx, hy]
    .
      have z: 2 ∣ 3 := by
        rw [← rn]
        simp
      norm_num at z
    .
      simp at rn
      replace rn: 19 * d = 1 := by omega
      have o1: d < 1 := by nlinarith [rn]
      omega

    norm_num

  -- case2: x > y, similar as above
  .
    replace l: y < x := by
      by_contra! l1
      simp at l
      have e: x = y := by linarith
      simp [e] at o
    have l': b < a := by
      simp [hx, hy]
      nlinarith
    have eq1: 8 * a ^ a * b ^ b = (a ^ b * b ^ b) * (8 * a ^ (a - b)) := by
      have o1: a ^ a = a ^ b * a ^ (a - b) := by
        nth_rewrite 2 [show a = a - b + b by omega]
        rw [Nat.pow_add]
        ring
      rw [o1]
      ring
    rw [eq1] at h
    clear eq1
    have eq2: 27 * a ^ b * b ^ a = (a ^ b * b ^ b) * (27 * b ^ (a - b)) := by
      have o1: b ^ a = b ^ b * b ^ (a - b) := by
        nth_rewrite 1 [show a = a - b + b by omega]
        rw [Nat.pow_add]
        ring
      rw [o1]
      ring
    rw [eq2] at h
    clear eq2
    have hp: 0 < a ^ b * b ^ b := by
      have o1: 0 < a ^ b := by
        apply Nat.pow_pos
        exact ha
      have o2: 0 < b ^ b := by
        apply Nat.pow_pos
        exact hb
      nlinarith
    apply Nat.mul_left_cancel hp at h
    clear hp
    have eq1: 8 * a ^ (a - b) = d ^ (d * x - d * y) * (8 * x ^ (d * x - d * y)) := by
      simp [hx, hy]
      ring
    have eq2: 27 * b ^ (a - b) = d ^ (d * x - d * y) * (27 * y ^ (d * x - d * y)) := by
      simp [hx, hy]
      ring
    rw [eq1, eq2] at h
    clear eq1 eq2
    have hp: 0 < d ^ (d * x - d * y) := by
        apply Nat.pow_pos
        by_contra! o
        replace o: d = 0 := by omega
        simp [o] at dx
        omega
    apply Nat.mul_left_cancel hp at h
    clear hp
    set i:= d * x - d * y with hi
    have oi: 0 < i := by
          simp [i]
          omega

    -- then we have x ∣ 27, hence x = 3 ^ m
    have ux: ∃ m, x = 3 ^ m := by
      have ox: x ∣ 27 := by
        have o1: x ∣ 8 * x ^ i := by
          have eq: x ^ i = x ^ (i - 1) * x := by
            nth_rewrite 1 [show i = i - 1 + 1 by omega]
            ring
          rw [eq]
          rw [show 8 * (x ^ (i - 1) * x) = 8 * x ^ (i - 1) * x by ring]
          simp
        rw [h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        exact pp
      replace ox: x ∈ Nat.divisors 27 := by
        simp
        exact ox
      have eq: Nat.divisors 27 = {1, 3, 9, 27} := by
        native_decide
      rw [eq] at ox
      clear eq
      simp at ox
      rcases ox with u | u | u | u
      .
        use 0
        simp [u]
      .
        use 1
        simp [u]
      .
        use 2
        simp [u]
      .
        use 3
        simp [u]
    obtain ⟨m, hm⟩ := ux

    -- similar for y
    have uy: ∃ n, y = 2 ^ n := by
      have oy: y ∣ 8 := by
        have o1: y ∣ 27 * y ^ i := by
          have eq: y ^ i = y ^ (i - 1) * y := by
            nth_rewrite 1 [show i = i - 1 + 1 by omega]
            ring
          rw [eq]
          rw [show 27 * (y ^ (i - 1) * y) = 27 * y ^ (i - 1) * y by ring]
          simp
        rw [← h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        apply Nat.Coprime.symm
        exact pp
      replace oy: y ∈ Nat.divisors 8 := by
        simp
        exact oy
      have eq: Nat.divisors 8 = {1, 2, 4, 8} := by
        native_decide
      rw [eq] at oy
      clear eq
      simp at oy
      rcases oy with u | u | u | u
      .
        use 0
        simp [u]
      .
        use 1
        simp [u]
      .
        use 2
        simp [u]
      .
        use 3
        simp [u]
    obtain ⟨n, hn⟩ := uy

    -- then we show that mi = ni = 3
    simp [hm, hn] at h
    rw [show (3 ^ m) ^ i = 3 ^ (m * i) by rw [← Nat.pow_mul]] at h
    rw [show (2 ^ n) ^ i = 2 ^ (n * i) by rw [← Nat.pow_mul]] at h
    have rm: m * i = 3 := by
      have l1: 27 ∣ 3 ^ (m * i) := by
        have o1: 27 ∣ 27 * 2 ^ (n * i) := by
          simp
        rw [← h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_left at o1
        exact o1
        norm_num
      have l2: 3 ^ (m * i) ∣ 27 := by
        have o1: 3 ^ (m * i) ∣ 8 * 3 ^ (m * i) := by
          simp
        rw [h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        apply Nat.Coprime.pow_left
        norm_num
      have r1: 3 ^ (m * i) = 27 := by
        apply Nat.dvd_antisymm
        exact l2
        exact l1
      rw [show 27 = 3 ^ 3 by norm_num] at r1
      rw [pow_right_inj₀] at r1
      exact r1
      norm_num
      norm_num

    -- similar for n
    have rn: n * i = 3 := by
      have l1: 8 ∣ 2 ^ (n * i) := by
        have o1: 8 ∣ 8 * 3 ^ (m * i) := by
          simp
        rw [h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_left at o1
        exact o1
        norm_num
      have l2: 2 ^ (n * i) ∣ 8 := by
        have o1: 2 ^ (n * i) ∣ 27 * 2 ^ (n * i) := by
          simp
        rw [← h] at o1
        apply Nat.Coprime.dvd_of_dvd_mul_right at o1
        exact o1
        apply Nat.Coprime.pow_right
        apply Nat.Coprime.pow_left
        norm_num
      have r1: 2 ^ (n * i) = 8 := by
        apply Nat.dvd_antisymm
        exact l2
        exact l1
      rw [show 8 = 2 ^ 3 by norm_num] at r1
      rw [pow_right_inj₀] at r1
      exact r1
      norm_num
      norm_num

    -- then we can check all finite cases
    have s: m = n := by
      rw [← rn] at rm
      nlinarith
    have en: n ∣ 3 := by
      rw [← rn]
      simp
    apply Nat.le_of_dvd at en
    simp [s] at hm
    simp [hm, hn] at hi
    simp [hi] at rn
    interval_cases n
    .
      simp at rn
    .
      simp at rn
      replace rn: d = 3 := by omega
      simp [hm, hn, rn] at hx hy
      simp [hx, hy]
    .
      have z: 2 ∣ 3 := by
        rw [← rn]
        simp
      norm_num at z
    .
      simp at rn
      replace rn: 19 * d = 1 := by omega
      have o1: d < 1 := by nlinarith [rn]
      omega

    norm_num