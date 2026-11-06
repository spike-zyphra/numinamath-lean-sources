import Mathlib

lemma lemma1 {a b: ℤ} (la: 0 < a) (lb: 0 < b) (h: 49 * a ^ 2 + b ^ 2 = 2009):
    a = 4 ∧ b = 35 ∨ a = 5 ∧ b = 28 := by
  have d: 7 ∣ b ^ 2 := by
    rw [show b ^ 2 = 2009 - 49 * a ^ 2 by omega]
    apply Int.dvd_sub
    .
      norm_num
    .
      rw [show 49 * a ^ 2 = 7 * (7 * a ^ 2) by ring]
      simp
  have o: Prime (7: ℤ) := by norm_num
  apply Prime.dvd_of_dvd_pow o at d
  clear o
  apply exists_eq_mul_right_of_dvd at d
  obtain ⟨k, hk⟩ := d
  simp [hk] at *
  replace h: a ^ 2 = 41 - k ^ 2 := by nlinarith
  have lk: k < 7 := by nlinarith
  interval_cases k
  .
    simp at h
    have l1: 6 < a := by nlinarith
    have l2: a < 7 := by nlinarith
    omega
  .
    simp at h
    have l1: 6 < a := by nlinarith
    have l2: a < 7 := by nlinarith
    omega
  .
    simp at h
    have l1: 5 < a := by nlinarith
    have l2: a < 6 := by nlinarith
    omega
  .
    simp at h
    rw [show (25: ℤ) = 5 ^ 2 by norm_num] at h
    rw [sq_eq_sq₀] at h
    simp [h]
    omega
    norm_num
  .
    simp at h
    rw [show (16: ℤ) = 4 ^ 2 by norm_num] at h
    rw [sq_eq_sq₀] at h
    simp [h]
    omega
    norm_num
  .
    simp at h
    have l1: 2 < a := by nlinarith
    have l2: a < 3 := by nlinarith
    omega


/-Given that the sum of the squares of four positive integers is 2009,
and the ratio of three of these numbers is 2:3:6, then these four numbers are-/

theorem number_theory_200648: {(a, b, c, d): ℤ × ℤ × ℤ × ℤ | 0 < d ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2009 ∧
  ∃ x, 0 < x ∧ a = 2 * x ∧ b = 3 * x ∧ c = 6 * x} = {(8, 12, 24, 35), (10, 15, 30, 28)} := by

    ext ⟨a, b, c, d⟩
    constructor

    -- the forward direction
    .
      simp only [Set.mem_setOf_eq]
      intro h
      rcases h with ⟨ld, h, hx⟩
      obtain ⟨x, hx⟩ := hx
      rcases hx with ⟨lx, ha, hb, hc⟩
      simp [ha, hb, hc] at *
      replace h: 49 * x ^ 2 + d ^ 2 = 2009 := by nlinarith
      have i:= lemma1 lx ld h
      rcases i with i | i
      .
        simp [i]
      .
        simp [i]


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h
      .
        simp [h]
        use 4
        norm_num
      .
        simp [h]
        use 5
        norm_num
