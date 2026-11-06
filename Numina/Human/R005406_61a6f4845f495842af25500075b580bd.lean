import Mathlib

/-Find the smallest positive integer that is twice a perfect square and three times a perfect cube.-/
theorem number_theory_608166: IsLeast {n: ℕ | ∃ a b: ℕ, (1 ≤ a) ∧ (1 ≤ b) ∧
 (n = 2 * a ^ 2) ∧ (n = 3 * b ^ 3)} 648 := by
  constructor
  -- 648 is in the set --
  . simp
    use 18
    simp
    use 6
    simp

  -- 648 is the least element of the set --
  . intro n
    intro hn
    simp at hn
    obtain ⟨a, ha, b, hb, h1, h2⟩ := hn
    have dvd2: 2 ∣3 * b ^ 3 := by
      rw [←h2]
      rw [h1]
      apply Nat.dvd_mul_right
    replace dvd2: 2 ∣ b ^ 3 := by
      have cop: Nat.Coprime 2 3 := by
        norm_num
      apply Nat.Coprime.dvd_of_dvd_mul_left cop dvd2
    replace dvd2: 2 ∣ b := by
      apply Nat.Prime.dvd_of_dvd_pow at dvd2
      exact dvd2
      norm_num
    apply exists_eq_mul_right_of_dvd at dvd2
    obtain ⟨c, hc⟩ := dvd2
    simp [hc] at h2
    have pow2: 2 ^ 3 ∣ n := by   -- The first part of the proof, 2 ^ 3 ∣ n --
      rw [h2]
      rw [show 3 * (2 * c) ^ 3 = 2 ^ 3 * (3 * c ^ 3) by ring]
      apply Nat.dvd_mul_right
    have dvd3: 3 ∣ n := by
      rw [h2]
      apply Nat.dvd_mul_right
    rw [h1] at dvd3
   -- now we need to show that 3 ^ 4 ∣ n - -
    replace dvd3 : 3 ∣ a ^ 2 := by
      have cop: Nat.Coprime 3 2 := by
        norm_num
      apply Nat.Coprime.dvd_of_dvd_mul_left cop dvd3
    replace dvd3: 3 ∣ a := by
      apply Nat.Prime.dvd_of_dvd_pow at dvd3
      tauto
      norm_num
    replace dvd3: 3 ^ 2 ∣ a ^ 2 := by
      rw [Nat.pow_dvd_pow_iff]
      exact dvd3
      omega
    have dvd3_n: 3 ^ 2 ∣ n := by
      rw [h1]
      omega
    rw [h2] at dvd3_n
    rw [show 3 ^ 2 = 3 * 3 by ring] at dvd3_n
    replace dvd3_n: 3 ∣ (2 * c) ^ 3 := by omega
    rw [show (2 * c) ^ 3 = 2 ^ 3 * (c ^ 3) by ring] at dvd3_n
    replace dvd3_n: 3 ∣ c ^ 3 := by
      have cop: Nat.Coprime 3 (2 ^ 3) := by
        norm_num
      apply Nat.Coprime.dvd_of_dvd_mul_left cop dvd3_n
    replace dvd3_n: 3 ∣ c := by
      apply Nat.Prime.dvd_of_dvd_pow at dvd3_n
      tauto
      norm_num
    apply exists_eq_mul_right_of_dvd at dvd3_n
    obtain ⟨d, hd⟩ := dvd3_n
    simp [hd] at h2
    ring_nf at h2
    have bd: 1 ≤ d := by
      by_contra! no
      replace no: d = 0 := by omega
      simp [no] at h2
      simp [h2] at h1
      rw [h1] at ha
      tauto
    rw [h2]
    have bd2: 1 ≤ d ^ 3 := by
      nlinarith
    omega