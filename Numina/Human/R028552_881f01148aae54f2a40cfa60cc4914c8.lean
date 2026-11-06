import Mathlib

/-A triple of positive integers (a,b,c) is tasty if lcm(a,b,c) | a + b + c - 1 and
a < b < c. Find the sum of a + b + c across all tasty triples.-/
theorem number_theory_610532: {(a, b, c): ℕ × ℕ × ℕ | 0 < a ∧ a < b ∧ b < c ∧ (a.lcm b).lcm c ∣ a + b + c - 1} =
 {(3, 4, 6), (6, 10 ,15)} := by
  ext ⟨a,b,c⟩
  simp only [Set.mem_setOf_eq]
  constructor
  -- the forward direction
  . intro h
    rcases h with ⟨ha,hab,hbc,h⟩
    simp
    have eq: b + a - 1 = c := by  -- we show the key equation
      have o: c ∣ (a.lcm b).lcm c := by
        apply Nat.dvd_lcm_right
      have d:= dvd_trans o h
      have d2: c ∣ b + a - 1 := by
        rw [show b + a - 1 = (a + b + c - 1) - c by omega]
        apply Nat.dvd_sub
        omega
        exact d
        simp
      apply exists_eq_mul_right_of_dvd at d2
      obtain ⟨k, hk⟩:= d2
      have l: k ≤ 1 := by
        by_contra! no
        replace l: 2 ≤ k := by omega
        have l1: 2 * c ≤ c * k := by nlinarith
        rw [← hk] at l1
        absurd l1
        simp
        omega
      have ne: k ≠ 0 := by
        by_contra! no
        simp [no] at hk
        omega
      have vk: k = 1 := by omega
      simp [vk] at hk
      exact hk
    have db: b ∣ a + c - 1 := by
      have o: b ∣ (a.lcm b).lcm c := by
        have o1: b ∣ a.lcm b := by
          apply Nat.dvd_lcm_right
        have o2: a.lcm b ∣ (a.lcm b).lcm c := by
          apply Nat.dvd_lcm_left
        apply dvd_trans o1 o2
      have d:= dvd_trans o h
      rw [show a + c - 1 = (a + b + c - 1) - b by omega]
      apply Nat.dvd_sub
      omega
      exact d
      simp
    have da: a ∣ c + b - 1 := by
      have o: a ∣ (a.lcm b).lcm c := by
        have o1: a ∣ a.lcm b := by
          apply Nat.dvd_lcm_left
        have o2: a.lcm b ∣ (a.lcm b).lcm c := by
          apply Nat.dvd_lcm_left
        apply dvd_trans o1 o2
      have d:= dvd_trans o h
      rw [show c + b - 1 = (a + b + c - 1) - a by omega]
      apply Nat.dvd_sub
      omega
      exact d
      simp
    simp [← eq] at da db
    rw [show b + a - 1 + b - 1 = (2 * b - 2) + a by omega] at da
    rw [show a + (b + a - 1) - 1 = (2 * a - 2) + b by omega] at db
    replace da: a ∣ 2 * b - 2 := by
      rw [show 2 * b - 2 = ((2 * b - 2) + a) - a by omega]
      apply Nat.dvd_sub
      omega
      exact da
      simp
    replace db: b ∣ 2 * a - 2 := by
      rw [show 2 * a - 2 = ((2 * a - 2) + b) - b by omega]
      apply Nat.dvd_sub
      omega
      exact db
      simp
    apply exists_eq_mul_right_of_dvd at db
    obtain ⟨k, hk⟩:= db
    have l: k ≤ 1 := by
      by_contra! no
      replace l: 2 ≤ k := by omega
      have l1: 2 * b ≤ b * k := by nlinarith
      rw [← hk] at l1
      absurd l1
      simp
      omega
    replace l: k = 0 ∨ k = 1 := by omega
    rcases l with l | l
    -- cases k = 0
    . simp [l] at hk
      omega
    -- cases k = 1
    . simp [l] at hk
      simp [← hk] at da
      rw [show 2 * (2 * a - 2) - 2 = 4 * a - 6 by omega] at da
      have i: a ∣ 6 := by
        rw [show 6 = 4 * a - (4 * a - 6) by omega]
        apply Nat.dvd_sub
        omega
        simp
        exact da
      apply Nat.le_of_dvd at i
      interval_cases a
      all_goals omega

  -- the backward direction
  . intro h
    simp at h
    rcases h with h | h
    all_goals simp [h]; norm_num
