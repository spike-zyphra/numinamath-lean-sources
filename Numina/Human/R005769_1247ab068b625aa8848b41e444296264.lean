import Mathlib


lemma l₁ {p : ℕ} {x y : ℕ}
  (pos_x : 0 < x) (pos_y : 0 < y) (prime_p : Nat.Prime p) :
  padicValNat p (x.gcd y) = min (padicValNat p x) (padicValNat p y)
    := by
  have := @Nat.factorization_gcd x y pos_x.ne.symm pos_y.ne.symm
  apply congrArg (· p) at this
  simpa [<- Nat.factorization_def _ prime_p]

lemma l₂ {a p : ℕ} (prime_p : Nat.Prime p) :
  padicValNat p (a^2) = 2 * padicValNat p a
    := by
  by_cases a_ne_0 : a = 0
  · subst a; simp
  rw [pow_two, two_mul]
  exact padicValNat.mul (hp := Fact.mk prime_p) a_ne_0 a_ne_0

lemma l₃ {b p : ℕ} (prime_p : Nat.Prime p) :
  padicValNat p (b^3) = 3 * padicValNat p b
    := by
  by_cases b_ne_0 : b = 0
  · subst b; simp
  have : 3 * padicValNat p b = padicValNat p b + 2 * padicValNat p b := by
    linarith
  rw [pow_three, this]
  rw [padicValNat.mul (hp := Fact.mk prime_p) b_ne_0
    (Nat.mul_ne_zero b_ne_0 b_ne_0)
  ]
  simp [two_mul]
  exact padicValNat.mul (hp := Fact.mk prime_p) b_ne_0 b_ne_0

lemma l₆ {n : ℕ} :
  2 ∣ n →
  n ≡ 0 [MOD 6] ∨ n ≡ 2 [MOD 6] ∨ n ≡ 4 [MOD 6]
    := by
  rintro ⟨ k, k_eq ⟩
  rw [k_eq]
  suffices 2*k ≡ 2*0 [MOD 6] ∨ 2*k ≡ 2*1 [MOD 6] ∨ 2*k ≡ 2*2 [MOD 6] by
    norm_num at this
    exact this
  rw [show 6 = 2*3 by rfl]
  simp only [Nat.ModEq.mul_left_cancel_iff' (show 2 ≠ 0 by linarith)]
  mod_cases k % 3
    <;> simp_all

lemma l₇ {n : ℕ} :
  3 ∣ n →
   n ≡ 0 [MOD 6] ∨ n ≡ 3 [MOD 6]
    := by
  rintro ⟨ j, j_eq ⟩
  rw [j_eq]
  suffices 3*j ≡ 3*0 [MOD 6] ∨ 3*j ≡ 3*1 [MOD 6] by
    norm_num at this
    exact this
  rw [show 6 = 3*2 by rfl]

  simp only [Nat.ModEq.mul_left_cancel_iff' (show 3 ≠ 0 by linarith)]
  mod_cases j % 2
    <;> simp_all

lemma l₈ {n : ℕ} :
  (∃ k j,  n = min (2*k) (3*j)) →
  n ≡ 0 [MOD 6] ∨ n ≡ 2 [MOD 6] ∨
  n ≡ 3 [MOD 6] ∨ n ≡ 4 [MOD 6]
    := by
  rintro ⟨ k, j, n_eq_min ⟩
  have : n = 2 * k ∨ n = 3 * j := by
    omega
  rcases this with (eq_k | eq_j)
  · have := @l₆ n ⟨ k, eq_k ⟩
    rcases this with (_|_|_) <;> simp_all
  · have := @l₇ n ⟨ j, eq_j ⟩
    cases this <;> simp_all

lemma l₁₀ {p : ℕ} (prime_p : Nat.Prime p) (p_gt_7 : p > 7)
    : p ≥ 11 := by
  by_contra! lt
  interval_cases p
  · apply Nat.not_prime_of_dvd_of_ne
      (show 2 ∣ 8 by norm_num) (by linarith) (by linarith)
    assumption
  · apply Nat.not_prime_of_dvd_of_ne
      (show 3 ∣ 9 by norm_num) (by linarith) (by linarith)
    assumption
  · apply Nat.not_prime_of_dvd_of_ne
      (show 2 ∣ 10 by norm_num) (by linarith) (by linarith)
    assumption

lemma l₁₁ (n p a b : ℕ) (prime_p : Nat.Prime p)
  (p_gt_7 : p > 7) (n_le_100 : n ≤ 100) (padic_eq :
    padicValNat p n = padicValNat p (a^2) ∨
    padicValNat p n = padicValNat p (b^3)
  )
    : padicValNat p n = 0 := by

  simp [padicValNat]
  intro p_ne_1 pos_n p_dvd_n
  have n_ge_p : n ≥ p := Nat.le_of_dvd (by linarith) p_dvd_n

  have p_sq_gt_100 : p^2 > 100 := by
    calc p^2
      _ ≥ 11^2 := by
        gcongr
        exact l₁₀ prime_p p_gt_7
      _ = 121 := by norm_num
      _ > 100 := by norm_num

  have val_n_lt : padicValNat p n < 2 := by
    have : n < p^2 := by
      exact Nat.lt_of_le_of_lt n_le_100 p_sq_gt_100
    simp [padicValNat]
    split_ifs
    · simp
      use 1
      simp
      exact Nat.not_dvd_of_pos_of_lt pos_n this
    · simp

  rcases padic_eq with (a_eq | b_eq)
  · have two_val_a_le_1 : 2 * padicValNat p a ≤ 1 := by
      rw [← l₂ prime_p, <- a_eq]
      exact Nat.le_of_lt_succ val_n_lt

    have val_a_eq_zero : padicValNat p a = 0 := by
      rw [two_mul] at two_val_a_le_1
      omega

    have val_a2_eq_zero : padicValNat p (a^2) = 0 := by
      rw [l₂ prime_p]
      omega

    have val_n_eq_zero : padicValNat p n = 0 := by
      omega

    simp [padicValNat] at val_n_eq_zero
    omega

  · have three_val_b_le_1 : 3 * padicValNat p b ≤ 1 := by
      rw [← l₃ prime_p, <- b_eq]
      exact Nat.le_of_lt_succ val_n_lt

    have val_b_eq_zero : padicValNat p b = 0 := by
      omega

    have val_b2_eq_zero : padicValNat p (b^3) = 0 := by
      rw [l₃ prime_p]
      omega

    have val_n_eq_zero : padicValNat p n = 0 := by
      omega

    simp [padicValNat] at val_n_eq_zero
    omega

theorem number_theory_609819 {n} {s : Finset ℕ} (pos_n : 0 < n) (n_le_100 : n ≤ 100)
  (s_eq : s = { 1, 4, 8, 9, 16, 25, 27, 36, 49, 64, 72, 81, 100 })
  (n_gcd_ab : ∃ a > 0, ∃ b > 0, n = Nat.gcd (a^2) (b^3)) :
  n ∈ s ∧ s.card = 13
    := by
  refine And.intro ?_ (by simp [s_eq])

  simp [s_eq]
  obtain ⟨ a, pos_a, b, pos_b, n_eq ⟩ := n_gcd_ab

  have padic_eq {p} (prime_p : Nat.Prime p) := by
    have := l₁ (x := a^2) (y := b^3)
      (Nat.pow_pos pos_a) (Nat.pow_pos pos_b) prime_p
    rw [<- n_eq] at this
    exact this

  have padic_mod {p} (prime_p : Nat.Prime p) :
      padicValNat p n ≡ 0 [MOD 6] ∨ padicValNat p n ≡ 2 [MOD 6] ∨
      padicValNat p n ≡ 3 [MOD 6] ∨ padicValNat p n ≡ 4 [MOD 6]
        := by
    specialize padic_eq prime_p
    obtain ⟨ k, k_eq ⟩ := Dvd.intro (padicValNat p a)
      (@l₂ a p prime_p).symm
    obtain ⟨ j, j_eq ⟩ := Dvd.intro (padicValNat p b)
      (@l₃ b p prime_p).symm
    rw [k_eq, j_eq] at padic_eq
    exact @l₈ (padicValNat p n) ⟨ k, j, padic_eq ⟩

  have padic_eq_0 : ∀ p > 7, Nat.Prime p → padicValNat p n = 0 := by
    intro p p_gt_7 prime_p
    specialize padic_eq prime_p
    have :
      padicValNat p n = padicValNat p (a ^ 2) ∨
      padicValNat p n = padicValNat p (b ^ 3)
        := by
      rw [min_def] at padic_eq
      split_ifs at padic_eq with this
      · exact Or.inl padic_eq
      · exact Or.inr padic_eq

    exact l₁₁ n p a b prime_p p_gt_7 n_le_100 this

  have n_prod : n = 2 ^ padicValNat 2 n * 3 ^ padicValNat 3 n * 5 ^ padicValNat 5 n * 7 ^ padicValNat 7 n := by
    have n_prod := Nat.prod_pow_prime_padicValNat n (by linarith) 101 (by linarith)
    replace n_prod : n = ∏ p ∈ Finset.range 101 with Nat.Prime p, p ^ padicValNat p n :=
      n_prod.symm
    replace n_prod : n = ∏ p ∈ (Finset.range 11 ∪ Finset.Ico 11 101) with Nat.Prime p, p ^ padicValNat p n := by
      exact n_prod
    rw [Finset.filter_union] at n_prod
    rw [Finset.prod_union (by
      rw [Finset.range_eq_Ico]
      suffices Disjoint (Finset.Ico 0 11) (Finset.Ico 11 101) by
        exact Finset.disjoint_filter_filter this
      apply Finset.Ico_disjoint_Ico_consecutive
    )] at n_prod

    have : ∏ p ∈ Finset.Ico 11 101 with Nat.Prime p, p ^ padicValNat p n =
        ∏ p ∈ Finset.Ico 11 101 with Nat.Prime p, 1 := by
      congr! 1 with p hp
      simp at hp
      have : 11 ≤ p := hp.left.left
      simp [padic_eq_0 p (by omega) hp.right]
    conv_rhs at this => simp
    simp [this] at n_prod
    conv_lhs => rw [n_prod]
    have : ∏ x ∈ Finset.range 11 with Nat.Prime x, x ^ padicValNat x n =
      ∏ x ∈ {2, 3, 5, 7}, x ^ padicValNat x n := by
      rfl

    rw [this]
    simp [mul_assoc, Nat.factorization_lcm]

  have pos_padic2 : 0 < 2 ^ padicValNat 2 n := by
    exact Nat.pos_of_neZero (2 ^ padicValNat 2 n)
  have pos_padic3 : 0 < 3 ^ padicValNat 3 n := by
    exact Nat.pos_of_neZero (3 ^ padicValNat 3 n)
  have pos_padic5 : 0 < 5 ^ padicValNat 5 n := by
    exact Nat.pos_of_neZero (5 ^ padicValNat 5 n)
  have pos_padic7 : 0 < 7 ^ padicValNat 7 n := by
    exact Nat.pos_of_neZero (7 ^ padicValNat 7 n)

  have padic_7 : padicValNat 7 n < 3 := by
    rw [n_prod] at n_le_100
    simp [mul_assoc] at n_le_100
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic2
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic3
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic5
    by_contra! gt2
    have : 7 ^ 3 ≤ 7 ^ padicValNat 7 n := by
      gcongr
      · simp

    have : 7 ^ 3 ≤ 100 := by
      exact Nat.le_trans this n_le_100

    simp at this

  replace padic_7 : padicValNat 7 n = 0 ∨ padicValNat 7 n = 2 := by
    interval_cases padic_eq : (padicValNat 7 n) <;>
      try simp
    specialize padic_mod (by norm_num : Nat.Prime 7)
    rw [padic_eq] at *
    rcases padic_mod with (_|_|_|_)
      <;> contradiction

  have padic_5 : padicValNat 5 n < 3 := by
    rw [n_prod] at n_le_100
    simp [mul_assoc] at n_le_100
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic2
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic3
    rw [mul_comm] at n_le_100
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic7
    by_contra! gt2
    have : 5 ^ 3 ≤ 5 ^ padicValNat 5 n := by
      gcongr
      · simp

    have : 5 ^ 3 ≤ 100 := by
      exact Nat.le_trans this n_le_100

    simp at this


  replace padic_5 : padicValNat 5 n = 0 ∨ padicValNat 5 n = 2 := by
    interval_cases padic_eq : (padicValNat 5 n) <;>
      try simp
    specialize padic_mod Nat.prime_five
    rw [padic_eq] at *
    rcases padic_mod with (_|_|_|_)
      <;> contradiction

  have padic_3 : padicValNat 3 n < 5 := by
    rw [n_prod] at n_le_100
    simp [mul_assoc] at n_le_100
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic2
    rw [mul_comm, mul_assoc] at n_le_100
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic5
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic7
    by_contra! gt2
    have : 3 ^ 5 ≤ 3 ^ padicValNat 3 n := by
      gcongr
      · simp

    have : 3 ^ 5 ≤ 100 := by
      exact Nat.le_trans this n_le_100

    simp at this

  replace padic_3: padicValNat 3 n = 0 ∨ padicValNat 3 n = 2 ∨
    padicValNat 3 n = 3 ∨ padicValNat 3 n = 4
      := by
    interval_cases padic_eq : (padicValNat 3 n) <;>
      try simp
    specialize padic_mod Nat.prime_three
    rw [padic_eq] at *
    rcases padic_mod with (_|_|_|_)
      <;> try contradiction

  have padic_2 : padicValNat 2 n < 7 := by
    rw [n_prod] at n_le_100
    simp [mul_assoc] at n_le_100
    rw [mul_comm, mul_assoc] at n_le_100
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic3
    rw [mul_assoc] at n_le_100
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic5
    replace n_le_100 := le_of_mul_le_of_one_le_right n_le_100 pos_padic7
    by_contra! gt2
    have : 2 ^ 7 ≤ 2 ^ padicValNat 2 n := by
      gcongr
      · simp

    have : 2 ^ 7 ≤ 100 := by
      exact Nat.le_trans this n_le_100

    simp at this

  replace padic_2 : padicValNat 2 n = 0 ∨ padicValNat 2 n = 2 ∨
      padicValNat 2 n = 3 ∨ padicValNat 2 n = 4 ∨
      padicValNat 2 n = 6 := by
    specialize padic_mod Nat.prime_two
    interval_cases h : (padicValNat 2 n) <;>
      simp

    all_goals rcases padic_mod with (h₂ | h₂ | h₂ | h₂)
        <;> try contradiction

  rcases padic_7 with (h₇ | h₇) <;>
  rcases padic_2 with (h₂ | h₂ | h₂ | h₂ | h₂) <;>
  rcases padic_3 with (h₃ | h₃ | h₃ | h₃) <;>
  rcases padic_5 with (h₅ | h₅)
  all_goals
    rw [h₂, h₃, h₅, h₇] at n_prod
    simp at n_prod
    omega
