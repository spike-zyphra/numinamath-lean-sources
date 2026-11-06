import Mathlib
/- Find all pairs of positive integers $x, y$ which satisfy the equation
$$
2 x^{2}+5 y^{2}=11(x y-11) \text {. }
$$ -/
theorem algebra_241101: {(x,y): ℤ × ℤ | x > 0 ∧ y > 0 ∧ 2 * x^2 + 5 * y^2 = 11 * (x * y - 11)}
 = {(14,27)} := by
  ext ⟨x,y⟩
  constructor
  -- the forward direction
  . intro h
    simp at h
    simp
    rcases h with ⟨hx,hy,h⟩
    replace h: -(2 * x^2 + 5 * y^2 - 11 * x * y) = 121 := by 
      linarith
    have o: - (2 * x^2 + 5 * y^2 - 11 * x * y) = (2 * x - y) * (5 * y - x) := by 
      ring
    rw [o] at h
    clear o
    have h1: 0 ≤ 2 * x - y := by
      by_contra! no
      have h2: 5 * y - x < 0 := by nlinarith
      replace no: 10 * x < 5 * y := by nlinarith
      replace h2: 5 * y < x := by nlinarith
      have contra: 10 * x < x := by nlinarith
      absurd contra
      simp
      nlinarith
    have h2: 0 ≤ 5 * y - x := by
      by_contra! h2
      have no: 2 * x - y < 0 := by nlinarith
      replace no: 10 * x < 5 * y := by nlinarith
      replace h2: 5 * y < x := by nlinarith
      have contra: 10 * x < x := by nlinarith
      absurd contra
      simp
      nlinarith
    set a:= 2 * x - y with ha
    set b:= 5 * y - x with hb
    have dvd: 11 ∣ a * b := by
      rw [h]
      omega
    apply Prime.dvd_or_dvd at dvd
    rcases dvd with dvd | dvd
    -- case 1: 11 ∣ a --
    . apply exists_eq_mul_right_of_dvd at dvd
      obtain ⟨k, hk⟩ := dvd
      simp [hk] at h
      replace h: k * b = 11 := by nlinarith
      have dvd2: 11 ∣ k * b := by
        rw [h]
      apply Prime.dvd_or_dvd at dvd2
      rcases dvd2 with dvd2 | dvd2
      -- case 1.1: 11 ∣ k --
      . apply exists_eq_mul_right_of_dvd at dvd2
        obtain ⟨k2, hk2⟩ := dvd2
        simp [hk2] at h
        replace h: k2 * b = 1 := by nlinarith
        have h':= h
        apply Int.eq_one_of_mul_eq_one_right at h
        apply Int.eq_one_of_mul_eq_one_left at h'
        simp [h] at hk2
        simp [hk2] at hk
        simp [ha] at hk
        simp [h'] at hb
        replace hk: y = 2 * x - 121 := by nlinarith
        simp [hk] at hb
        ring_nf at hb
        replace hb: 9 * x = 606 := by linarith
        replace hb: (9: ℤ) ∣ 606 := by
          rw [← hb]
          omega
        all_goals omega
      -- case 1.2: 11 ∣ b --
      . apply exists_eq_mul_right_of_dvd at dvd2
        obtain ⟨k2, hk2⟩ := dvd2
        simp [hk2] at h
        replace h: k2 * k = 1 := by nlinarith
        have h':= h
        apply Int.eq_one_of_mul_eq_one_right at h
        apply Int.eq_one_of_mul_eq_one_left at h'
        simp [h] at hk2
        simp [h'] at hk
        rw [ha] at hk
        rw [hb] at hk2
        replace hk: y = 2 * x - 11:= by nlinarith
        simp [hk] at hk2
        ring_nf at hk2
        replace ha: 9 * x = 66 := by linarith
        replace ha: (9: ℤ) ∣ 66 := by
          rw [← ha]
          omega
        all_goals omega
      norm_num
    -- case 2: 11 ∣ b --
    . apply exists_eq_mul_right_of_dvd at dvd
      obtain ⟨k, hk⟩ := dvd
      simp [hk] at h
      replace h: k * a = 11 := by nlinarith
      have dvd2: 11 ∣ k * a := by
        rw [h]
      apply Prime.dvd_or_dvd at dvd2
      rcases dvd2 with dvd2 | dvd2
      -- case 1.1: 11 ∣ k --
      . apply exists_eq_mul_right_of_dvd at dvd2
        obtain ⟨k2, hk2⟩ := dvd2
        simp [hk2] at h
        replace h: k2 * a = 1 := by nlinarith
        have h':= h
        apply Int.eq_one_of_mul_eq_one_right at h
        apply Int.eq_one_of_mul_eq_one_left at h'
        simp [h] at hk2
        simp [hk2] at hk
        simp [hb] at hk
        simp [h'] at ha
        replace hk: x = 5 * y - 121 := by nlinarith
        simp [hk] at ha
        ring_nf at ha
        replace hb: 9 * y = 243 := by linarith
        replace hb: y = 27 := by linarith
        simp [hb] at hk
        all_goals omega
      -- case 1.2: 11 ∣ b --
      . apply exists_eq_mul_right_of_dvd at dvd2
        obtain ⟨k2, hk2⟩ := dvd2
        simp [hk2] at h
        replace h: k2 * k = 1 := by nlinarith
        have h':= h
        apply Int.eq_one_of_mul_eq_one_right at h
        apply Int.eq_one_of_mul_eq_one_left at h'
        simp [h'] at hk
        simp [h] at hk2
        simp [hk2] at ha
        simp [hk] at hb
        replace ha: y = 2 * x - 11:= by nlinarith
        simp [ha] at hb
        ring_nf at hb
        replace ha: 9 * x = 66 := by linarith
        replace ha: (9: ℤ) ∣ 66 := by
          rw [← ha]
          omega
        all_goals omega
      norm_num
    norm_num
  -- the backward direction --
  . intro h
    simp at h
    simp
    simp [h]
