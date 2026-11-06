import Mathlib


lemma l₁ {p a b : ℕ} (hp : p.Prime)
  (eq : p^2 = a^2 + 2*b^2)
  (pos_b : b ≠ 0)
  : Nat.gcd a b = 1 := by
  rw [<- Nat.coprime_iff_gcd_eq_one]
  by_contra! not_coprime
  obtain ⟨ k, prime_k, k_dvd_a, k_dvd_b ⟩ := by
    rwa [Nat.Prime.not_coprime_iff_dvd] at not_coprime

  obtain ⟨ u, u_eq ⟩ := k_dvd_a
  obtain ⟨ j, j_eq ⟩ := k_dvd_b

  subst a b
  replace eq : p^2 = k ^ 2 * (u ^ 2 + j ^ 2 * 2) := by
    linear_combination eq

  have : k ∣ p := by
    have : k ∣ k ^ 2 * (u ^ 2 + j ^ 2 * 2) := by
      rw [sq k, mul_assoc]
      exact Nat.dvd_mul_right k (k * (u ^ 2 + j ^ 2 * 2))

    have : k ∣ p^2 := by rwa [<- eq] at this
    exact Nat.Prime.dvd_of_dvd_pow prime_k this

  have : k = p := by
    exact (Nat.prime_dvd_prime_iff_eq prime_k hp).mp this

  subst k
  simp_all
  have : 0 < j := by omega
  suffices  j ^ 2 > 0 by omega
  exact Nat.pow_pos this

lemma gcd_sq_diff {p a b : ℕ} (hp : p.Prime)
  (gcd_ab : Nat.gcd a b = 1)
  (a_le_p : a < p)
  (eq : 2*b^2 = (p - a) * (p + a))
  (pos_b : b ≠ 0)
  : Nat.gcd (p-a) (p+a) = 2 := by

  obtain ⟨ ⟨ k, k_eq ⟩, ⟨ j, j_eq ⟩ ⟩ := Nat.gcd_dvd (p - a) (p + a)

  generalize m_eq : (p - a).gcd (p + a) = m at *

  replace two_a : (p + a) - (p - a) = m*j - m*k := by
    rw [<- k_eq, <- j_eq]

  replace two_a : 2*a = m*(j - k) := by
    rw [two_mul]
    convert two_a using 1
    have : p + a ≥ p - a := by omega
    rw [Nat.add_sub_sub_cancel a_le_p.le]
    rw [Nat.mul_sub]

  rw [<- m_eq]

  have a_ne_0 : a ≠ 0 := by
    intro eq
    subst a
    simp_all

    have m_ne_0 : m ≠ 0 := by
      intro m_eq
      subst m_eq
      simp_all
    have k_eq_j : k = j := by
      simpa [m_ne_0] using j_eq

    have : m = 1 := by
      by_contra! h
      have ge_2 : m ≥ 2 := by omega
      replace ge_mul : 2 ≥ m * (m * (k * j)) := by linarith
      replace ge_mul : 2 ≥ 2 * (m * (k * j)) := by
        exact mul_le_of_mul_le_right ge_mul ge_2
      have : j - k = 0 := by simp_all
      by_cases hj : 0 = j
      · simp_all
      ·
        have pos_j : 0 < j := by
          exact Nat.zero_lt_of_ne_zero fun a ↦ hj (id (Eq.symm a))
        have : 0 < k := by
          linarith
        have : 0 < k * j := by
          exact Nat.mul_pos this pos_j
        rw [<- mul_assoc] at ge_mul
        replace ge_mul : 1 ≥ m * (k * j) := by
          linarith
        replace ge_mul : 1 ≥ 2 * (k * j) := by
          exact mul_le_of_mul_le_right ge_mul ge_2
        omega
    subst this
    simp_all

  have pos_gcd : m ≠ 0 := by
    intro m_eq
    rw [m_eq] at k_eq j_eq
    simp_all

  have coprime : Nat.Coprime k j := by
    have : 0 < m := by
      exact Nat.zero_lt_of_ne_zero pos_gcd
    have := Nat.coprime_div_gcd_div_gcd (by rwa [<- m_eq] at this)
    rw [m_eq] at *
    rw [mul_comm] at k_eq j_eq
    convert this
    ·
      apply congrArg (· / m) at k_eq
      have : k * m / m = k := by
        field_simp
      rw [this] at k_eq
      exact k_eq.symm
    ·
      apply congrArg (· / m) at j_eq
      have : j * m / m = j := by
        field_simp
      rw [this] at j_eq
      exact j_eq.symm

  have : 2 ∣ p - a ∨ 2 ∣ p + a := by
    apply (Nat.Prime.dvd_mul (Nat.prime_two)).mp
    rw [<- eq]
    exact Nat.dvd_mul_right 2 (b ^ 2)

  obtain ⟨ two_dvd_sub, two_dvd_add ⟩ : 2 ∣ p - a ∧ 2 ∣ p + a := by
    omega


  replace : 2^2 ∣ (p - a) * (p + a) := by
    exact Nat.mul_dvd_mul two_dvd_sub two_dvd_add
  replace two_dvd : 2 ∣ b^2 := by
    omega

  suffices m = 2 by rwa [m_eq]


  have gcd_ge_2 : m > 1 := by
    have : m ≠ 1 := by
      by_contra! eq
      subst eq
      have dvd2k : 2 ∣ k := by
        simp_all
      have dvd2j : 2 ∣ j := by
        simp_all

      have := Nat.not_coprime_of_dvd_of_dvd (by linarith) dvd2k dvd2j
      exact this coprime

    omega

  have gcd_self : Nat.gcd (p - a) (p + a) = Nat.gcd (p - a) (p - a + p + a) := by
    have := (Nat.gcd_self_add_right (p - a) (p + a))
    conv_lhs at this => simp [<- add_assoc]
    rw [this]
  replace gcd_self : (p - a).gcd (p + a) = (p - a).gcd (2 * p) := by
    convert gcd_self using 2
    omega

  have coprime_diff : p.gcd (p - a) = 1 := by
    have coprime_pa : Nat.Coprime p a := by
      have := Nat.Prime.coprime_iff_not_dvd hp (n := a)
      rw [this]
      rintro ⟨ n, n_eq ⟩
      have : 0 < n := by
        suffices n ≠ 0 by
          exact Nat.zero_lt_of_ne_zero this
        intro eq
        simp_all

      simp_all
      have : 0 < p := by
        exact Nat.zero_lt_of_lt a_le_p

      conv at a_le_p => rhs; rw [<- one_mul p]
      field_simp at a_le_p
      linarith

    have := Nat.Prime.coprime_iff_not_dvd hp (n := p - a)
    simp [this]
    have diff : p - a < p := by omega
    rintro ⟨ n, n_eq ⟩
    simp [n_eq] at *
    have : n ≠ 0 := by
      intro eq
      subst eq
      simp_all
    have : 0 < n := by
      exact Nat.zero_lt_of_ne_zero this
    have : p < p := lt_of_mul_lt_of_one_le_left diff this
    simp at this


  have coprime2p_diff : Nat.gcd (2*p) (p - a) = 2 := by
    obtain ⟨ l, l_eq ⟩ := two_dvd_sub
    rw [l_eq] at coprime_diff
    rw [l_eq]
    rw [Nat.gcd_mul_left]
    field_simp
    exact Nat.Coprime.coprime_mul_left_right coprime_diff

  rw [<- m_eq]
  rw [gcd_self]
  rw [Nat.gcd_comm]
  exact coprime2p_diff


theorem number_theory_31008 {p : ℕ} {A : Set ℕ}
  (prime : p.Prime)
  (hA : A = { n | ∃ a b : ℤ, n.cast = a^2 + 2 * b^2 ∧ b ≠ 0})
  (p_sq_in_A : p^2 ∈ A) : p ∈ A := by
  have : A = { n | ∃ a b : ℕ, n = a^2 + 2 * b^2 ∧ b ≠ 0} := by
    rw [hA]
    ext n
    zify
    constructor
    · intro s
      conv_rhs at hA =>
        rhs; intro x
        rhs; intro a
        rhs; intro b
        rw [<- Int.natAbs_sq a, <- Int.natAbs_sq b]
        rw [<- Int.natAbs_ne_zero]
      obtain ⟨ a, b, n_eq, b_ne_0 ⟩ := s
      use a.natAbs, b.natAbs
      simp_all
    · intro s
      aesop

  subst this
  simp_all [<- hA]

  obtain ⟨a, b, eq, b_ne_0⟩ := p_sq_in_A


  have h_eq : p^2 = a^2 + 2 * b^2 := by
    simp [<- eq]

  have factored : 2 * b^2 = (p - a) * (p + a) := by
    have : 2 * b^2 = p^2 - a^2 := by
      exact Eq.symm (Nat.sub_eq_of_eq_add' eq)

    rwa [Nat.sq_sub_sq, mul_comm (p + a)] at this

  have h_gcd : Nat.gcd a b = 1 := l₁ prime h_eq b_ne_0

  have gcd_sq_diff : Nat.gcd (p - a) (p + a) = 2 := by
    apply gcd_sq_diff prime h_gcd ?_ factored b_ne_0
    have : 0 < 2*b^2 := by positivity
    have : a ^ 2 < p ^ 2 := by
      omega

    exact (sq_lt_sq₀ (by simp) (by simp)).mp this

  have h_div : 2 ∣ (p - a) ∧ 2 ∣ (p + a) := by
    have : 2 ∣ Nat.gcd (p - a) (p + a) := by
      rw [gcd_sq_diff]
    exact Nat.dvd_gcd_iff.mp this

  obtain ⟨m, m_eq⟩ := h_div.left
  obtain ⟨n, n_eq⟩ := h_div.right

  have coprime : Nat.gcd m n = 1 := by
    rw [m_eq, n_eq] at gcd_sq_diff
    conv_rhs at gcd_sq_diff => rw [<- mul_one 2]
    rw [Nat.gcd_mul_left] at gcd_sq_diff
    apply congrArg (· / 2) at gcd_sq_diff
    convert gcd_sq_diff using 1
    field_simp

  have hb_even : Even b := by
    rw [m_eq, n_eq] at factored
    apply congrArg (· / 2) at factored
    field_simp at factored
    replace factored : b ^ 2 = 2 * (m * n) := by
      convert factored using 1
      field_simp [mul_assoc]
      linarith

    have : 2 ∣ b^2 := by
      exact Dvd.intro (m * n) (id (Eq.symm factored))

    replace : Even (b^2) := by
      exact (even_iff_exists_two_nsmul (b ^ 2)).mpr this

    simpa [Nat.even_pow] using this

  obtain ⟨β, β_eq⟩ := hb_even
  rw [<- mul_two] at β_eq

  have mn_β_sq : 4 * β ^ 2 = 2 * m * n := by
    rw [m_eq, n_eq, β_eq] at factored
    apply congrArg (· / 2) at factored
    field_simp at factored
    convert factored using 1
    · ring
    · ring_nf
      rw [show 4 = 2 * 2 by rfl]
      field_simp [<- mul_assoc]


  replace mn_β_sq : m * n = 2 * β^2 := by
    apply congrArg (· / 2) at mn_β_sq
    field_simp at mn_β_sq
    convert mn_β_sq.symm using 1
    · ring_nf
      field_simp [<- mul_assoc]
    · ring_nf
      rw [show 4 = 2 * 2 by rfl]
      field_simp [<- mul_assoc]

  by_cases even_m : Even m
  ·
    have h_odd_n : Odd n := by
      rw [<- Nat.not_even_iff_odd]
      intro h_even_n
      have : 2 ∣ Nat.gcd m n := by
        have two_dvd_n : 2 ∣ n := by exact even_iff_two_dvd.mp h_even_n
        have two_dvd_m : 2 ∣ m := by exact even_iff_two_dvd.mp even_m
        exact Nat.dvd_gcd two_dvd_m two_dvd_n

      rw [coprime] at this
      simp at this

    obtain ⟨ u, u_eq ⟩ := even_m
    obtain ⟨r, u_eq_r_sq⟩ : ∃ r, u = r^2 := by
      rw [<- mul_two] at u_eq
      rw [u_eq] at mn_β_sq coprime
      replace coprime : u.gcd n = 1 := by
        exact Nat.Coprime.coprime_mul_right coprime

      have un_β : u * n = β^2 := by
        linarith

      zify at un_β coprime
      have := Int.sq_of_gcd_eq_one (by simpa using coprime) un_β

      obtain ⟨ s, s_eq ⟩ := this
      use s.natAbs
      rcases s_eq with (h | h)
      · zify
        simp [h]
      · by_contra! u_eq
        zify [h] at u_eq
        simp at u_eq
        have : s ≠ 0 := by
          intro s_eq
          subst s_eq
          simp_all
          have : 0 = β^2 := by
            zify [un_β]
          have : β = 0 := by
            exact pow_eq_zero this.symm

          exact b_ne_0 this

        have : 0 < s^2 := by
          rw [<- Int.natAbs_sq]
          norm_cast
          have : 0 < s.natAbs := by
            exact Int.natAbs_pos.mpr this

          exact Nat.pow_pos this

        linarith

    obtain ⟨s, n_eq_s_sq⟩ : ∃ s, n = s^2 := by
      rw [<- mul_two] at u_eq
      rw [u_eq] at mn_β_sq coprime
      replace coprime : n.gcd u = 1 := by
        have := Nat.Coprime.coprime_mul_right coprime
        exact Nat.coprime_comm.mp this

      have un_β : n * u = β^2 := by
        linarith

      zify at un_β coprime
      have := Int.sq_of_gcd_eq_one (by simpa using coprime) un_β

      obtain ⟨ s, s_eq ⟩ := this
      use s.natAbs
      rcases s_eq with (h | h)
      · zify
        simp [h]
      · by_contra! u_eq
        zify [h] at u_eq
        simp at u_eq
        have : s ≠ 0 := by
          intro s_eq
          subst s_eq
          simp_all
          have : 0 = β^2 := by
            zify [un_β]
          have : β = 0 := by
            exact pow_eq_zero this.symm

          exact b_ne_0 this

        have : 0 < s^2 := by
          rw [<- Int.natAbs_sq]
          norm_cast
          have : 0 < s.natAbs := by
            exact Int.natAbs_pos.mpr this

          exact Nat.pow_pos this

        linarith

    have r_ne_0 : ¬r = 0 := by
      aesop

    rw [u_eq, u_eq_r_sq, n_eq_s_sq] at mn_β_sq
    have h_rβ : 2 * r^2 * s^2 = 2 * β^2 := by
      linear_combination mn_β_sq

    have p_eq : p = s^2 + 2 * r^2 := by
      rw [u_eq, u_eq_r_sq, n_eq_s_sq] at coprime
      rw [<- two_mul] at u_eq
      rw [<- n_eq_s_sq, <- u_eq_r_sq, <- u_eq]
      suffices 2 * p = 2 * n + 2 * m by linarith
      rw [<- m_eq, <- n_eq]
      have : a ≤ p := by
        have : 0 < 2*b^2 := by positivity
        have : a ^ 2 ≤ p ^ 2 := by
          omega

        exact (sq_le_sq₀ (by simp) (by simp)).mp this

      omega

    exact ⟨s, r, ⟨ p_eq, r_ne_0 ⟩⟩
  ·
    simp at even_m
    have odd_m := even_m
    clear even_m

    have even_n : Even n := by
      by_contra! odd_n
      simp at odd_n

      have even_mn : Even (m * n) := by
        use β^2
        simp [mn_β_sq, two_mul]
      have odd_mn : Odd (m * n) := by
        exact Odd.mul odd_m odd_n

      rw [<- Nat.not_even_iff_odd] at odd_mn
      exact odd_mn even_mn

    obtain ⟨ u, u_eq ⟩ := even_n
    obtain ⟨r, u_eq_r_sq⟩ : ∃ r, u = r^2 := by
      rw [<- mul_two] at u_eq
      rw [u_eq] at mn_β_sq coprime
      replace coprime : u.gcd m = 1 := by
        apply Nat.Coprime.symm at coprime
        exact Nat.Coprime.coprime_mul_right coprime

      have un_β : u * m = β^2 := by
        linarith

      zify at un_β coprime
      have := Int.sq_of_gcd_eq_one (by simpa using coprime) un_β

      obtain ⟨ s, s_eq ⟩ := this
      use s.natAbs
      rcases s_eq with (h | h)
      · zify
        simp [h]
      · by_contra! u_eq
        zify [h] at u_eq
        simp at u_eq
        have : s ≠ 0 := by
          intro s_eq
          subst s_eq
          simp_all
          have : 0 = β^2 := by
            zify [un_β]
          have : β = 0 := by
            exact pow_eq_zero this.symm

          exact b_ne_0 this

        have : 0 < s^2 := by
          rw [<- Int.natAbs_sq]
          norm_cast
          have : 0 < s.natAbs := by
            exact Int.natAbs_pos.mpr this

          exact Nat.pow_pos this

        linarith

    obtain ⟨s, m_eq_s_sq⟩ : ∃ s, m = s^2 := by
      rw [<- mul_two] at u_eq
      rw [u_eq] at mn_β_sq coprime
      replace coprime : m.gcd u = 1 := by
        exact Nat.Coprime.coprime_mul_right_right coprime

      have um_β : m * u = β^2 := by
        linarith

      zify at um_β coprime
      have := Int.sq_of_gcd_eq_one (by simpa using coprime) um_β

      obtain ⟨ s, s_eq ⟩ := this
      use s.natAbs
      rcases s_eq with (h | h)
      · zify
        simp [h]
      · by_contra! u_eq
        zify [h] at u_eq
        simp at u_eq
        have : s ≠ 0 := by
          intro s_eq
          subst s_eq
          simp_all
          have : 0 = β^2 := by
            zify [um_β]
          have : β = 0 := by
            exact pow_eq_zero this.symm

          exact b_ne_0 this

        have : 0 < s^2 := by
          rw [<- Int.natAbs_sq]
          norm_cast
          have : 0 < s.natAbs := by
            exact Int.natAbs_pos.mpr this

          exact Nat.pow_pos this

        linarith

    have r_ne_0 : ¬r = 0 := by
      aesop

    rw [u_eq, u_eq_r_sq, m_eq_s_sq] at mn_β_sq
    have h_rβ : 2 * r^2 * s^2 = 2 * β^2 := by
      linear_combination mn_β_sq

    have p_eq : p = s^2 + 2 * r^2 := by
      rw [u_eq, u_eq_r_sq, m_eq_s_sq] at coprime
      rw [<- two_mul] at u_eq
      rw [<- m_eq_s_sq, <- u_eq_r_sq, <- u_eq]
      suffices 2 * p = 2 * n + 2 * m by linarith
      rw [<- m_eq, <- n_eq]
      have : a ≤ p := by
        have : 0 < 2*b^2 := by positivity
        have : a ^ 2 ≤ p ^ 2 := by
          omega

        exact (sq_le_sq₀ (by simp) (by simp)).mp this

      omega

    exact ⟨s, r, ⟨ p_eq, r_ne_0 ⟩⟩
