import Mathlib

set_option maxHeartbeats 600000

/-Do there exist ten pairwise distinct natural numbers such that their arithmetic mean is

a) exactly six times;

b) exactly five times;

their greatest common divisor?-/

theorem number_theory_179176: (∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℕ,
  0 < a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 < a6 ∧
  a6 < a7 ∧ a7 < a8 ∧ a8 < a9 ∧ a9 < a10 ∧
  (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) / (10: ℚ) =
  6 * a1.gcd (a2.gcd (a3.gcd (a4.gcd (a5.gcd (a6.gcd (a7.gcd (a8.gcd (a9.gcd a10)))))))))
  ∧ (¬ ∃ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : ℕ,
  0 < b1 ∧ b1 < b2 ∧ b2 < b3 ∧ b3 < b4 ∧ b4 < b5 ∧ b5 < b6 ∧
  b6 < b7 ∧ b7 < b8 ∧ b8 < b9 ∧ b9 < b10 ∧
  (b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10) / (10: ℚ) =
  5 * b1.gcd (b2.gcd (b3.gcd (b4.gcd (b5.gcd (b6.gcd (b7.gcd (b8.gcd (b9.gcd b10))))))))) := by

  constructor

  -- the first part: show existence of a1, a2, ..., a10
  .
    use 1
    use 2
    use 3
    use 4
    use 5
    use 6
    use 7
    use 8
    use 9
    use 15
    norm_num

 -- the second part: show there are no b1, b2, ..., b10
  .
    intro h
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, h⟩ := h
    set d:= b1.gcd (b2.gcd (b3.gcd (b4.gcd (b5.gcd (b6.gcd (b7.gcd (b8.gcd (b9.gcd b10))))))))

    -- then we have to show that d ∣ b1, d ∣ b2, ..., d ∣ b10 step by step
    have d1: d ∣ b1 := by
      apply Nat.gcd_dvd_left
    set f2:= b2.gcd (b3.gcd (b4.gcd (b5.gcd (b6.gcd (b7.gcd (b8.gcd (b9.gcd b10)))))))
    have g2: d ∣ f2 := by
      apply Nat.gcd_dvd_right
    have d2: d ∣ b2 := by
      have o: f2 ∣ b2 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g2 o
    set f3:= b3.gcd (b4.gcd (b5.gcd (b6.gcd (b7.gcd (b8.gcd (b9.gcd b10))))))
    have l3: f2 ∣ f3 := by
      apply Nat.gcd_dvd_right
    have g3: d ∣ f3 := by
      apply dvd_trans g2 l3
    have d3: d ∣ b3 := by
      have o: f3 ∣ b3 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g3 o
    set f4:= b4.gcd (b5.gcd (b6.gcd (b7.gcd (b8.gcd (b9.gcd b10)))))
    have l4: f3 ∣ f4 := by
      apply Nat.gcd_dvd_right
    have g4: d ∣ f4 := by
      apply dvd_trans g3 l4
    have d4: d ∣ b4 := by
      have o: f4 ∣ b4 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g4 o
    set f5:= b5.gcd (b6.gcd (b7.gcd (b8.gcd (b9.gcd b10))))
    have l5: f4 ∣ f5 := by
      apply Nat.gcd_dvd_right
    have g5: d ∣ f5 := by
      apply dvd_trans g4 l5
    have d5: d ∣ b5 := by
      have o: f5 ∣ b5 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g5 o
    set f6:= b6.gcd (b7.gcd (b8.gcd (b9.gcd b10)))
    have l6: f5 ∣ f6 := by
      apply Nat.gcd_dvd_right
    have g6: d ∣ f6 := by
      apply dvd_trans g5 l6
    have d6: d ∣ b6 := by
      have o: f6 ∣ b6 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g6 o
    set f7:= b7.gcd (b8.gcd (b9.gcd b10))
    have l7: f6 ∣ f7 := by
      apply Nat.gcd_dvd_right
    have g7: d ∣ f7 := by
      apply dvd_trans g6 l7
    have d7: d ∣ b7 := by
      have o: f7 ∣ b7 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g7 o
    set f8:= b8.gcd (b9.gcd b10)
    have l8: f7 ∣ f8 := by
      apply Nat.gcd_dvd_right
    have g8: d ∣ f8 := by
      apply dvd_trans g7 l8
    have d8: d ∣ b8 := by
      have o: f8 ∣ b8 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g8 o
    set f9:= b9.gcd b10
    have l9: f8 ∣ f9 := by
      apply Nat.gcd_dvd_right
    have g9: d ∣ f9 := by
      apply dvd_trans g8 l9
    have d9: d ∣ b9 := by
      have o: f9 ∣ b9 := by
        apply Nat.gcd_dvd_left
      apply dvd_trans g9 o
    have d10: d ∣ b10 := by
      have o: f9 ∣ b10 := by
        apply Nat.gcd_dvd_right
      apply dvd_trans g9 o
    clear g2 g3 g4 g5 g6 g7 g8 g9
    clear l3 l4 l5 l6 l7 l8 l9
    clear_value f2 f3 f4 f5 f6 f7 f8 f9

    -- then we need to show that i ≤ ki step by step
    apply exists_eq_mul_right_of_dvd at d1
    obtain ⟨k1, h1⟩ := d1
    have r1: 1 ≤ k1 := by nlinarith
    have o: d ≠ 0 := by
      by_contra! o
      simp [o] at h1
      simp [h1] at s1
    apply exists_eq_mul_right_of_dvd at d2
    obtain ⟨k2, h2⟩ := d2
    have r2: 2 ≤ k2 := by
      simp [h1, h2] at s2
      apply Nat.lt_of_mul_lt_mul_left at s2
      omega
    apply exists_eq_mul_right_of_dvd at d3
    obtain ⟨k3, h3⟩ := d3
    have r3: 3 ≤ k3 := by
      simp [h2, h3] at s3
      apply Nat.lt_of_mul_lt_mul_left at s3
      omega
    apply exists_eq_mul_right_of_dvd at d4
    obtain ⟨k4, h4⟩ := d4
    have r4: 4 ≤ k4 := by
      simp [h3, h4] at s4
      apply Nat.lt_of_mul_lt_mul_left at s4
      omega
    apply exists_eq_mul_right_of_dvd at d5
    obtain ⟨k5, h5⟩ := d5
    have r5: 5 ≤ k5 := by
      simp [h4, h5] at s5
      apply Nat.lt_of_mul_lt_mul_left at s5
      omega
    apply exists_eq_mul_right_of_dvd at d6
    obtain ⟨k6, h6⟩ := d6
    have r6: 6 ≤ k6 := by
      simp [h5, h6] at s6
      apply Nat.lt_of_mul_lt_mul_left at s6
      omega
    apply exists_eq_mul_right_of_dvd at d7
    obtain ⟨k7, h7⟩ := d7
    have r7: 7 ≤ k7 := by
      simp [h6, h7] at s7
      apply Nat.lt_of_mul_lt_mul_left at s7
      omega
    apply exists_eq_mul_right_of_dvd at d8
    obtain ⟨k8, h8⟩ := d8
    have r8: 8 ≤ k8 := by
      simp [h7, h8] at s8
      apply Nat.lt_of_mul_lt_mul_left at s8
      omega
    apply exists_eq_mul_right_of_dvd at d9
    obtain ⟨k9, h9⟩ := d9
    have r9: 9 ≤ k9 := by
      simp [h8, h9] at s9
      apply Nat.lt_of_mul_lt_mul_left at s9
      omega
    apply exists_eq_mul_right_of_dvd at d10
    obtain ⟨k10, h10⟩ := d10
    have r10: 10 ≤ k10 := by
      simp [h9, h10] at s10
      apply Nat.lt_of_mul_lt_mul_left at s10
      omega
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at h
    qify at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10
    have o1: 0 < d := by omega
    qify at o1

    -- note that left side of h is more than right side
    have u: 5 * (d: ℚ) <
  (↑d * ↑k1 + ↑d * ↑k2 + ↑d * ↑k3 + ↑d * ↑k4 + ↑d * ↑k5 + ↑d * ↑k6 + ↑d * ↑k7 + ↑d * ↑k8 + ↑d * ↑k9 + ↑d * ↑k10) / 10 := by
      nlinarith
    rw [h] at u
    simp at u
    