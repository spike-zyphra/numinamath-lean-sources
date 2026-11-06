import Mathlib


lemma l₀ {M x y} (h_div : M * x * y ∣ x^2 + y^2 - x)
  : ∃ m : ℕ, x^2 + y^2 - x = m*x*y := by
  obtain ⟨ m, m_eq ⟩ := h_div
  rw [m_eq]
  use M * m
  ring

lemma l₁ {M x y} (h_div : M * x * y ∣ x^2 + y^2 - x)
  : ∃ m : ℕ, x^2 - x = y * (m*x - y) := by
  obtain ⟨ m, m_eq ⟩ := h_div
  suffices ∃ m, x ^ 2 - x = x * y * m - y^2 by
    convert this using 3 with m
    simp [Nat.mul_sub]
    ring_nf
  replace m_eq : x ^ 2 - x = M * x * y * m - y ^ 2 := by omega
  use M * m
  convert m_eq using 1
  ring_nf

lemma l₂ {M x y} (h_div : M * x * y ∣ x^2 + y^2 - x)
  : ∃ m : ℕ, m*x*y - (x^2 - x) = y^2 := by
  obtain ⟨ m, m_eq ⟩ := l₀ h_div
  use m
  rw [<- m_eq]
  rw [Nat.sub_sub_sub_cancel_right
    (by rw [sq]; exact Nat.le_mul_self x)]
  exact Nat.add_sub_self_left (x ^ 2) (y ^ 2)


lemma Nat.exists_eq_pow_two_of_prime_pow_two_dvd {n : ℕ} (pos_n : 0 < n)
  (h_even : ∀ p : ℕ, Prime p → Even (padicValNat p n)) :
  ∃ k : ℕ, n = k^2 := by
  have := Nat.prod_pow_prime_padicValNat n (by linarith : n ≠ 0) (n + 1) (by simp)
  have : (∏ p ∈ Finset.range (n + 1) with Prime p,
      p ^ (padicValNat p n / 2))^2 = n := by
    rw [sq]
    rw [<- Finset.prod_mul_distrib]
    simp [<- sq]

    convert this using 2 with p p_in
    simp at p_in
    specialize h_even p p_in.right
    obtain ⟨ j, j_eq ⟩ := h_even
    simp [j_eq, <- two_mul]
    ring

  rw [<- this]
  simp

lemma Nat.prime_pow_two_dvd_of_exists_eq_pow_two (n : ℕ) (pos_n : 0 < n) :
  (∃ k : ℕ, n = k^2) → ∀ p, Nat.Prime p → Even (padicValNat p n) := by
  rintro ⟨ k, n_eq_k_sq ⟩ p prime_p
  rw [n_eq_k_sq]
  rw [padicValNat.pow (hp := Fact.mk prime_p)]
  · simp
  · intro eq
    subst eq
    simp [n_eq_k_sq] at pos_n


lemma Nat.prime_pow_two_dvd_iff_exists_eq_pow_two {n : ℕ}
  (pos_n : 0 < n) :
  (∃ k : ℕ, n = k^2) ↔ (∀ p, Nat.Prime p → Even (padicValNat p n)) := by
  constructor
  · intro exists_sq
    exact prime_pow_two_dvd_of_exists_eq_pow_two n pos_n exists_sq
  · exact fun a ↦ exists_eq_pow_two_of_prime_pow_two_dvd pos_n a


theorem number_theory_635084 (M x y : ℕ)
  (pos_x : 0 < x) (pos_y : 0 < y) (h_div : M * x * y ∣ x^2 + y^2 - x) :
    ∃ k : ℕ, x = k^2 := by
  apply Nat.exists_eq_pow_two_of_prime_pow_two_dvd pos_x
  intro p prime_p
  have hp : Fact (Nat.Prime p) := { out := prime_p }
  by_contra! h
  simp at h
  obtain ⟨ j, j_eq ⟩ := h

  have dvd_x : x = 0 ∨ 2 * j + 1 ≤ padicValNat p x := by
    exact Or.inr (Nat.le_of_eq j_eq.symm)

  rw [<- padicValNat_dvd_iff] at dvd_x

  have dvd_x_sq : p ^ (2 * j + 1) ∣ x^2 - x := by
    rw [sq, show x * x - x = x * (x - 1) by
      exact Eq.symm (Nat.mul_sub_one x x)
    ]
    exact Dvd.dvd.mul_right dvd_x (x - 1)

  have dvd_x_y : p ^ (2*j + 1) ∣ x*y := by
    exact Dvd.dvd.mul_right dvd_x y

  have dvd_x_sq_y_sq_x : p ^ (2 * j + 1) ∣ x^2 + y^2 - x := by
    have : x ≤ x^2 := by
      rw [sq]
      exact Nat.le_mul_self x

    obtain ⟨ l, l_eq ⟩ := l₀ h_div
    rw [l_eq]
    rw [mul_assoc]
    exact Dvd.dvd.mul_left dvd_x_y l

  have dvd_y_sq : p ^ (2 * j + 1) ∣ y^2 := by
    obtain ⟨ m, m_eq ⟩ := l₂ h_div
    rw [<- m_eq]
    apply Nat.dvd_sub' (by
      rw [<- mul_comm x, mul_assoc]
      exact Dvd.dvd.mul_right dvd_x (m * y)
    ) (by exact dvd_x_sq)


  have pos_p : 0 < p := by
    exact Nat.Prime.pos prime_p

  have pos_y_sq : 0 < y^2 := by exact Nat.pow_pos pos_y

  have even_padic : ∃ k, y^2 = k^2 := by simp
  rw [Nat.prime_pow_two_dvd_iff_exists_eq_pow_two pos_y_sq] at even_padic
  specialize even_padic p prime_p

  have padic_x_le_padic_y_sq : padicValNat p x ≤ padicValNat p (y^2) := by
    rw [<- j_eq] at dvd_y_sq
    exact (padicValNat_dvd_iff_le
      (by exact Ne.symm (Nat.ne_of_lt pos_y_sq))
    ).mp dvd_y_sq

  replace dvd_y_sq : p ^ (2 * j + 2) ∣ y^2 := by
    rw [j_eq] at padic_x_le_padic_y_sq
    obtain ⟨ k, k_eq ⟩ := even_padic
    rw [<- mul_two] at k_eq
    rw [k_eq] at padic_x_le_padic_y_sq
    replace this : j < k := by linarith
    have : 2 * j + 2 ≤ padicValNat p (y ^ 2) := by
      omega

    rwa [<- padicValNat_dvd_iff_le ((Nat.ne_of_lt pos_y_sq).symm)] at this

  have dvd_y_x : p ^ (2 * j + 2) ∣ x * y := by
    have ⟨ a, a_eq ⟩ := dvd_y_sq
    rw [show 2 * j + 2 = 2 * (j + 1) by linarith] at a_eq dvd_y_sq
    rw [show p ^ (2 * (j + 1)) = (p^(j+1))^2 by
      rw [Nat.pow_mul']
    ] at a_eq dvd_y_sq

    obtain ⟨ b, b_eq ⟩ : ∃ b, a = b^2 := by
      rw [mul_comm] at a_eq
      have := IsSquare.mul (IsSquare.sq y) (IsSquare.sq (p ^ (j + 1)))
      rw [isSquare_iff_exists_sq] at this
      obtain ⟨ r, r_eq ⟩ := this
      use y / (p ^ (j + 1))
      have y_dvd_pj : p ^ (j + 1) ∣ y := by
        have : p ^ (j + 1) ∣ y^2 := by
          exact dvd_of_mul_left_dvd dvd_y_sq

        refine (padicValNat_dvd_iff_le pos_y.ne.symm
          (hp := by exact { out := prime_p })).mpr ?_

        obtain ⟨ k, k_eq ⟩ := even_padic
        rw [j_eq, k_eq] at padic_x_le_padic_y_sq
        rw [<- two_mul,
          padicValNat.pow 2 pos_y.ne.symm] at k_eq

        omega

      suffices a = y^2 / (p ^ (j + 1))^2 by
        convert this using 1
        rw [Nat.div_pow y_dvd_pj]

      have : y ^ 2 / (p ^ (j + 1)) ^ 2 = a * (p ^ (j + 1)) ^ 2 / (p ^ (j + 1)) ^ 2 := by
        exact congrFun (congrArg HDiv.hDiv a_eq) ((p ^ (j + 1)) ^ 2)

      field_simp at this
      exact this.symm

    subst a
    have : y = p^(j+1) * b := by
      rw [<- Nat.mul_pow] at a_eq
      apply congrArg Nat.sqrt at a_eq
      simp [Nat.sqrt_eq'] at a_eq
      exact a_eq

    rw [this]
    obtain ⟨ i, i_eq ⟩ := dvd_x
    rw [i_eq]
    rw [<- mul_comm i, mul_assoc]
    suffices p ^ (2 * j + 2) ∣ p ^ (2 * j + 1) * (p ^ (j + 1) * b) by
      exact Dvd.dvd.mul_left this i
    suffices p ^ (2 * j + 2) ∣ b * (p ^ (2 * j + 1) * p ^ (j + 1)) by
      convert this using 1
      ring

    apply Dvd.dvd.mul_left
    ring_nf
    suffices p ^ (j * 2) ∣ p ^ (j * 3) by
      exact Nat.mul_dvd_mul_left (p ^ 2) this

    simp [Nat.pow_mul]
    exact Dvd.intro (p ^ j) rfl

  obtain ⟨ m, m_eq ⟩ := l₀ h_div
  have : p^(2*j + 2) ∣ m*x*y := by
    rw [mul_assoc]
    exact Dvd.dvd.mul_left dvd_y_x m


  replace : p^(2*j + 2) ∣ x^2 + y^2 - x := by
    exact (Nat.ModEq.dvd_iff
      (congrFun (congrArg HMod.hMod (id (Eq.symm m_eq))) (y ^ 2))
      dvd_y_sq
    ).mp this

  replace dvd_x_sq : p^(2*j + 2) ∣ x^2 := by
    have dvd_sq : (p^(2*j + 1))^2 ∣ x^2 := by
      exact pow_dvd_pow_of_dvd dvd_x 2

    rw [<- Nat.pow_mul, mul_comm, mul_add] at dvd_sq
    simp [<- mul_assoc] at dvd_sq
    have : 2*j +2 ≤ 4*j + 2 := by
      linarith

    exact Nat.pow_dvd_of_le_of_pow_dvd this dvd_sq

  have dvd_add_sq : p^(2*j + 2) ∣ x^2 + y^2 - x := by
    have ⟨ m, m_eq ⟩ := l₀ h_div
    rw [m_eq]
    exact (Nat.ModEq.dvd_iff
      (congrFun (congrArg HMod.hMod m_eq) (y ^ 2)) dvd_y_sq
    ).mp this

  have dvd_add_sq : p^(2*j + 2) ∣ x^2 + y^2 := by
    exact (Nat.dvd_add_iff_right dvd_x_sq).mp dvd_y_sq

  have : p^(2*j + 2) ∣ x := by

    have : p^(2*j + 2) ∣ x^2 + y^2 - (x^2 + y^2 - x) := by
      exact Nat.dvd_sub' dvd_add_sq this

    replace : p^(2*j + 2) ∣ x^2 + y^2 - ((x^2 + y^2) - x) := by
      exact this

    replace : p^(2*j + 2) ∣ x^2 + y^2 - (x^2 + y^2) + x := by
      convert this using 1
      rw [Nat.sub_sub_self]
      · simp
      · suffices x ≤ x^2 by exact Nat.le_add_right_of_le this
        rw [sq]
        exact Nat.le_mul_self x

    convert this
    simp

  conv_lhs at this => rhs; rhs; rw [show 2 = 1 + 1 by rfl]
  rw [<- add_assoc, <- j_eq] at this

  contrapose! this
  exact pow_succ_padicValNat_not_dvd pos_x.ne.symm
