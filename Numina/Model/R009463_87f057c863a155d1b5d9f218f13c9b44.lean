import Mathlib

theorem number_theory_221758 (p a b c : ℤ) (hp : Prime p)
    (hpa : p ∣ a)(hpb : p ∣ b)(hpc : p ∣ c)
    (hroots : ∃ r s : ℤ, r ≠ s ∧
      r^3 + a * r^2 + b * r + c = 0 ∧
      s^3 + a * s^2 + b * s + c = 0) :
    p^3 ∣ c := by
  obtain ⟨r, s, r_ne_s, r_root, s_root⟩ := hroots
  have p_dvd_r3 : p ∣ r^3 := by
    have help1 : p ∣ - (a * r^2 + b * r + c) := by
      apply Dvd.dvd.neg_right
      apply dvd_add
      . apply dvd_add
        . exact Dvd.dvd.mul_right hpa (r ^ 2)
        . exact Dvd.dvd.mul_right hpb r
      . exact hpc
    have help2 : r^3 = - (a * r^2 + b * r + c) := by linarith
    rw [← help2] at help1
    exact help1
  have p_dvd_r : p ∣ r := Prime.dvd_of_dvd_pow hp p_dvd_r3
  have p_dvd_s3 : p ∣ s^3 := by
    have help1 : p ∣ - (a * s^2 + b * s + c) := by
      apply Dvd.dvd.neg_right
      apply dvd_add
      . apply dvd_add
        . exact Dvd.dvd.mul_right hpa (s ^ 2)
        . exact Dvd.dvd.mul_right hpb s
      . exact hpc
    have help2 : s^3 = - (a * s^2 + b * s + c) := by linarith
    rw [← help2] at help1
    exact help1
  have p_dvd_s : p ∣ s := Prime.dvd_of_dvd_pow hp p_dvd_s3
  have aux1 : r^3 - s^3 + a*(r^2 - s^2) + b*(r - s) = 0 := by linarith
  have aux2 : (r - s) * (r^2 + r*s + s^2 + a*(r + s) + b) = 0 := by linarith
  have aux3 : r^2 + r*s + s^2 + a*(r + s) + b = 0 := by
    apply mul_eq_zero.mp at aux2
    rcases aux2 with h | h
    . have r_eq_s : r = s := by linarith -- case: r - s = 0
      exact absurd r_eq_s r_ne_s
    . exact h -- case: $r^2 + r * s + s^2 + a*(r + s) + b = 0$
  have aux4 : p^2 ∣ -(r^2 + r*s + s^2 + a*(r + s)) := by
    have help1 : p^2 ∣ r^2 := by apply pow_dvd_pow_of_dvd p_dvd_r
    have help2 : p^2 ∣ r*s := by
      apply mul_dvd_mul
      simp
      . exact p_dvd_r
      . exact p_dvd_s
    have help3 : p^2 ∣ s^2 := by apply pow_dvd_pow_of_dvd p_dvd_s
    have help4 : p ∣ (r + s) := dvd_add p_dvd_r p_dvd_s
    have help5 : p^2 ∣ a*(r + s) := by
      apply mul_dvd_mul
      simp
      . exact hpa
      . exact help4
    apply Dvd.dvd.neg_right
    apply dvd_add
    . apply dvd_add
      . exact (Int.dvd_add_right help1).mpr help2
      . exact help3
    . exact help5
  have p2_div_b : p^2 ∣ b := by
    have help : b = -(r^2 + r*s + s^2 + a*(r + s)) := by linarith
    rw [← help] at aux4
    exact aux4
  have r_root : r^3 + a * r^2 + b * r + c = 0 := r_root
  have eq1 : c = - (r^3 + a * r^2 + b * r) := by linarith
  rw [eq1]
  apply dvd_neg.2
  apply dvd_add
  . apply dvd_add
    . have help1 : p^3 ∣ r^3 := by apply pow_dvd_pow_of_dvd p_dvd_r
      exact help1
    . have help2 : p^3 ∣ a * r^2 := by
        obtain ⟨a1, ha1⟩ := show p ∣ a by exact hpa
        obtain ⟨r1, hr1⟩ := show p ∣ r by exact p_dvd_r
        use a1 * r1^2
        rw [ha1, hr1]
        ring_nf
      exact help2
  . have help3 : p^3 ∣ b * r := by
      obtain ⟨b1, hb1⟩ := show p^2 ∣ b by exact p2_div_b
      obtain ⟨r1, hr1⟩ := show p ∣ r by exact p_dvd_r
      use b1 * r1
      rw [hb1, hr1]
      ring_nf
    exact help3