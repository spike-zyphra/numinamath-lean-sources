import Mathlib

lemma int_gcd_even {a b: ℤ} (ha : Even a) (hb : Even b) : Even (Int.gcd a b) := by
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  use Int.gcd a' b'
  rw [ha', hb']
  repeat rw [← two_mul]
  rw [Int.gcd_mul_left]
  norm_cast

lemma int_gcd_odd {a b: ℤ} (ha : Odd a) : Odd (Int.gcd a b) := by
  contrapose ha
  simp at ha ⊢
  obtain ⟨a', ha'⟩ := ha
  have h1: (2:ℤ) ∣ Int.gcd a b := by
    use a'
    rw [ha']
    norm_cast
    ring

  have h2 := @Int.gcd_dvd_left a b
  have h3 := Int.dvd_trans h1 h2
  rw [← even_iff_two_dvd] at h3
  exact h3

lemma int_gcd_dvd {a b c: ℤ} : Int.gcd (Int.gcd a b) c ∣ Int.gcd (Int.gcd (a + b) (b + c)) (c + a) := by
  let k : ℤ := Int.gcd (Int.gcd a b) c
  have h1 : k ∣ Int.gcd a b := Int.gcd_dvd_left
  have ha := Int.dvd_trans h1 (@Int.gcd_dvd_left a b)
  have hb := Int.dvd_trans h1 (@Int.gcd_dvd_right a b)
  have hc : k ∣ c := Int.gcd_dvd_right
  have hab := Int.dvd_add ha hb
  have hbc := Int.dvd_add hb hc
  have hca := Int.dvd_add hc ha
  have h2 := Int.dvd_gcd hab hbc
  have h3 := Int.dvd_gcd h2 hca
  unfold k at h3
  norm_cast at h3

theorem number_theory_607296 (x y z : ℤ) :
  (Int.gcd (Int.gcd x y) z < Int.gcd (Int.gcd (x + y) (y + z)) (z + x)) ↔
    ∃ k a b c: ℤ, Odd a ∧ Odd b ∧ Odd c ∧ 0 < k ∧ (x, y, z) = (k * a, k * b, k * c) := by


  constructor
  . intro h
    let k : ℤ := Int.gcd (Int.gcd x y) z
    let d : ℤ := Int.gcd (Int.gcd (x + y) (y + z)) (z + x)
    have : k ∣ Int.gcd x y := Int.gcd_dvd_left
    have hkx : k ∣ x := Int.dvd_trans this (@Int.gcd_dvd_left x y)
    have hky : k ∣ y := Int.dvd_trans this (@Int.gcd_dvd_right x y)
    have hkz : k ∣ z := Int.gcd_dvd_right

    have ⟨a, ha⟩ := hkx
    have ⟨b, hb⟩ := hky
    have ⟨c, hc⟩ := hkz

    have : d ∣ Int.gcd (x + y) (y + z) := Int.gcd_dvd_left
    have hdxy : d ∣ (x + y) := Int.dvd_trans this (@Int.gcd_dvd_left (x + y) (y + z))
    have hdyz : d ∣ (y + z) := Int.dvd_trans this (@Int.gcd_dvd_right (x + y) (y + z))
    have hdzx : d ∣ (z + x) := Int.gcd_dvd_right
    have hd2x : d ∣ 2 * x := by
      have := Int.dvd_add hdxy hdzx
      have := Int.dvd_sub this hdyz
      ring_nf at this
      ring_nf
      exact this

    have hd2y : d ∣ 2 * y := by
      have := Int.dvd_add hdxy hdyz
      have := Int.dvd_sub this hdzx
      ring_nf at this
      ring_nf
      exact this

    have hd2z : d ∣ 2 * z := by
      have := Int.dvd_add hdyz hdzx
      have := Int.dvd_sub this hdxy
      ring_nf at this
      ring_nf
      exact this

    have h1 : d ∣ Int.gcd (2 * x) (2 * y) := Int.dvd_gcd hd2x hd2y
    have h2 : d ∣ Int.gcd (Int.gcd (2 * x) (2 * y)) (2 * z) := Int.dvd_gcd h1 hd2z

    have h3 : d ∣ 2 * k := by
      rw [Int.gcd_mul_left] at h2
      push_cast at h2
      rw [Int.gcd_mul_left] at h2
      norm_cast at h2

    have h_k_pos : k > 0 := by
      by_contra hk
      have : k = 0 := by omega
      rw [this] at ha hb hc
      simp at ha hb hc
      subst x y z
      simp at h
    have h4 : d = 2 * k := by
      have : k ∣ d := by
        unfold k d
        norm_cast
        exact int_gcd_dvd

      obtain ⟨m, hm⟩ := h3
      obtain ⟨n, hn⟩ := this
      rw [hm]
      suffices m = 1 by rw [this]; simp
      rw [hn] at hm
      have : 2 = n * m := by nlinarith
      have : 0 < n := by
        suffices d > 0 by nlinarith
        unfold d
        norm_cast
        by_contra hd
        simp at hd
        rw [Int.gcd_eq_zero_iff] at hd
        obtain ⟨h1, h2⟩ := hd
        norm_cast at h1 h2
        rw [Int.gcd_eq_zero_iff] at h1
        obtain ⟨h3, h4⟩ := h1
        have hx: x = 0 := by omega
        have hy: y = 0 := by omega
        have hz: z = 0 := by omega
        rw [hx, hy, hz] at h
        simp at h

      have : n ≤ 2 := by
        apply Int.le_of_dvd
        . norm_num
        . use m

      interval_cases n
      . unfold k d at hn
        norm_cast at hn
        rw [hn] at h
        omega
      . linarith

    have h5 : Int.gcd (Int.gcd (a + b) (b + c)) (c + a) = 2 := by
      unfold d at h4
      rw [ha, hb, hc] at h4
      rw [show (k * a + k * b) = k * (a + b) by ring] at h4
      rw [show (k * b + k * c) = k * (b + c) by ring] at h4
      rw [show (k * c + k * a) = k * (c + a) by ring] at h4
      rw [Int.gcd_mul_left] at h4
      push_cast at h4
      rw [abs_of_pos h_k_pos] at h4
      rw [Int.gcd_mul_left] at h4
      push_cast at h4
      rw [abs_of_pos h_k_pos] at h4
      nlinarith

    have h6 : Even (a + b) ∧ Even (b + c) ∧ Even (c + a) := by
      have h6 := @Int.gcd_dvd_right (Int.gcd (a + b) (b + c)) (c + a)
      rw [h5] at h6
      norm_cast at h6
      rw [← even_iff_two_dvd] at h6

      have h7 := @Int.gcd_dvd_left (Int.gcd (a + b) (b + c)) (c + a)
      rw [h5] at h7

      have h8 := @Int.gcd_dvd_left (a + b) (b + c)
      have h9 := @Int.gcd_dvd_right (a + b) (b + c)

      have h10 := Int.dvd_trans h7 h8
      have h11 := Int.dvd_trans h7 h9

      norm_cast at h10 h11
      rw [← even_iff_two_dvd] at h10 h11
      exact ⟨h10, h11, h6⟩


    have h7 : Odd a ∧ Odd b ∧ Odd c := by
      obtain ⟨ h_even_ab, h_even_bc, h_even_ca ⟩ := h6
      by_contra h
      have : Even a ∧ Even b ∧ Even c := by
        simp at h
        by_cases ha1 : Odd a
        . have := Even.sub_odd h_even_ab ha1
          rw [show a + b - a = b by ring] at this
          have := h ha1 this
          have := Odd.add_even ha1 this
          contrapose this
          simp
          rw [add_comm]
          exact h_even_ca
        . simp at ha1
          refine ⟨ha1, ?_, ?_⟩
          . have := Even.sub h_even_ab ha1
            rw [show a + b - a = b by ring] at this
            exact this
          . have := Even.sub h_even_ca ha1
            rw [show c + a - a = c by ring] at this
            exact this

      obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩⟩ := this
      have h2kx : (2*k) ∣ x := by
        use a'
        rw [ha, ha']
        ring
      have h2ky : (2*k) ∣ y := by
        use b'
        rw [hb, hb']
        ring
      have h2kz : (2*k) ∣ z := by
        use c'
        rw [hc, hc']
        ring


      have := Int.dvd_gcd h2kx h2ky
      have : 2 * k ∣ k := Int.dvd_gcd this h2kz
      obtain ⟨m, hm⟩ := this
      have : k * (1 - 2 * m) = 0 := by linarith
      simp at this
      omega

    use k, a, b, c
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    . exact h7.1
    . exact h7.2.1
    . exact h7.2.2
    . exact h_k_pos
    . rw [ha, hb, hc]

  . rintro ⟨k, a, b, c, ha, hb, hc, hk, h⟩
    simp at h
    obtain ⟨h1, h2, h3⟩ := h
    subst x y z
    rw [Int.gcd_mul_left]
    rw [show k * a + k * b = k * (a + b) by ring]
    rw [show k * b + k * c = k * (b + c) by ring]
    rw [show k * c + k * a = k * (c + a) by ring]
    rw [Int.gcd_mul_left]
    push_cast
    rw [abs_of_pos hk]
    rw [Int.gcd_mul_left]
    rw [Int.gcd_mul_left]
    suffices Int.gcd (Int.gcd a b) c < Int.gcd (Int.gcd (a + b) (b + c)) (c + a) by
      have : k.natAbs > 0 := by omega
      nlinarith [this]

    have h1: Int.gcd (Int.gcd a b) c ≤ Int.gcd (Int.gcd (a + b) (b + c)) (c + a) := by
      apply Nat.le_of_dvd
      . by_contra h
        simp at h
        rw [Int.gcd_eq_zero_iff] at h
        obtain ⟨h2, h3⟩ := h
        norm_cast at h2
        rw [Int.gcd_eq_zero_iff] at h2
        obtain ⟨h4, h5⟩ := h2
        have : a = 0 := by omega
        subst a
        contrapose ha
        simp
      . exact int_gcd_dvd


    suffices Int.gcd (Int.gcd a b) c ≠ Int.gcd (Int.gcd (a + b) (b + c)) (c + a) by
      omega

    have h3: Even (Int.gcd (Int.gcd (a + b) (b + c)) (c + a)) := by
      apply int_gcd_even
      . norm_cast
        apply int_gcd_even
        . apply Odd.add_odd
          . exact ha
          . exact hb
        . apply Odd.add_odd
          . exact hb
          . exact hc
      . apply Odd.add_odd
        . exact hc
        . exact ha

    have h4: Odd (Int.gcd (Int.gcd a b) c) := by
      apply int_gcd_odd
      norm_cast
      apply int_gcd_odd
      exact ha

    contrapose h4
    simp at h4
    rw [h4]
    simp
    exact h3
