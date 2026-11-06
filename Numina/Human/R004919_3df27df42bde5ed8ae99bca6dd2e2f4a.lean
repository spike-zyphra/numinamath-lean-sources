import Mathlib


theorem prod_padic_eq_sum {s : Finset ℕ} (n : ℕ) {p} (prime_p : Prime p)
  (no_zeros : ∀ x ∈ s, x ≠ 0) (le_range : ∀ x ∈ s, x ≤ n)
  : padicValNat p (s.prod λ i => i ^ (n + 1 - i))
  = s.sum (λ i => padicValNat p (i ^ (n + 1 - i)))
  := by
  rw [<- Nat.prime_iff] at prime_p
  induction' s using Finset.induction_on with m s m_not_in ih
  case empty =>
    simp
  case insert =>
    simp_all
    obtain ⟨ m_ne_0, no_zeros ⟩ := no_zeros
    rw [padicValNat.mul (hp := Fact.mk prime_p)
      (by
        suffices 0 < (n + 1 - m) by
          exact pow_ne_zero (n + 1 - m) m_ne_0
        omega
      )
      (by
        apply Finset.prod_ne_zero_iff.mpr
        intro a a_in
        have a_ne_0 : a ≠ 0 := by
          intro a_eq
          subst a
          exact no_zeros a_in
        suffices 0 < (n + 1 - a) by
          exact pow_ne_zero (n + 1 - a) a_ne_0
        have := le_range.right a a_in
        omega
      )
    ]
    exact congrArg (HAdd.hAdd (padicValNat p (m ^ (n + 1 - m)))) ih

lemma vp1 (n p i : ℕ) (n_lt_p_sq : n < p^2) (p_dvd_i : p ∣ i) (i_le_n : i ≤ n)
    (pos_i : 0 < i) (prime_p : p.Prime): padicValNat p i = 1 := by
  have ⟨j, jeq⟩ := p_dvd_i

  subst jeq
  have pj_lt_p_sq : p * j < p^2 := by
    exact Nat.lt_of_le_of_lt i_le_n n_lt_p_sq

  have j_lt_p : j < p := by
    rw [sq] at pj_lt_p_sq
    have hjnot0 : j ≠ 0 := by
      intro eq
      subst j
      simp at pos_i

    exact (Nat.mul_lt_mul_left
      (by exact Nat.pos_of_dvd_of_pos p_dvd_i pos_i)).mp pj_lt_p_sq

  have pos_j : 0 < j := by
    exact Nat.pos_of_mul_pos_left pos_i

  have not_p_dvd_j : ¬ p ∣ j := by
    intro h_div
    have : j ≥ p := Nat.le_of_dvd pos_j h_div
    linarith

  have padic_self : padicValNat p p = 1 := by
    apply padicValNat.self
    exact Nat.Prime.one_lt prime_p

  have padic_sum : padicValNat p (p * j) = padicValNat p p + padicValNat p j := by
    have : Fact (Nat.Prime p) := by exact { out := prime_p }
    rw [padicValNat.mul] <;> linarith

  have padic_zero : padicValNat p j = 0 := by
    exact padicValNat.eq_zero_of_not_dvd not_p_dvd_j

  omega


lemma v_p_factorial_eq_sum (p k n : ℕ)
  (prime_p : Nat.Prime p)
  (k_eq : k = 2 ∨ k = 3)
  (kp_lt : k * p < n)
  (n_gt : 16 < n)
  (k_max : ¬∃ j, j > k ∧ j * p ≤ n)
  : padicValNat p (∏ i ∈ Finset.Ico 1 (n+1), i.factorial)
  = ∑ i ∈ Finset.Icc 1 k, (n + 1 - i*p)
  := by
  have pos_k : 0 < k := by omega
  have factorial_eq_prod {j} : j.factorial = ∏ x ∈ Finset.Ico 1 (j+1), x := by
    symm
    exact Finset.prod_Ico_id_eq_factorial j

  have factorial_eq_pow : ∏ i ∈ Finset.Icc 1 n, i.factorial
    = ∏ i ∈ Finset.Icc 1 n, i^(n + 1 - i) := by
    conv_lhs => rhs; intro i; rw [factorial_eq_prod]

    have : ∏ i ∈ Finset.Icc 1 n, ∏ x ∈ Finset.Ico 1 (i+1), x
      = (∏ m ∈ Finset.Icc 1 n, ∏ i ∈ Finset.Ico m (n+1), m)
      := by
      rw [Finset.prod_comm']
      simp
      intro x y
      omega

    rw [this]
    simp

  rw [show ∏ i ∈ Finset.Ico 1 (n + 1), i.factorial =
      ∏ i ∈ Finset.Icc 1 n, i.factorial by rfl
  ]

  simp [factorial_eq_pow]
  have prod_eq_sum := prod_padic_eq_sum n prime_p.prime
    (s := Finset.Icc 1 n)
    (by simp; intro x _ _ _; subst x; linarith)
    (by
      intro x x_in
      simp at x_in
      linarith
    )
  rw [prod_eq_sum]

  have no_zero : 0 ∉ Finset.Icc 1 k := by simp
  replace : ∑ i ∈ Finset.Icc 1 n, padicValNat p (i ^ (n + 1 - i))
    = ∑ i ∈ Finset.Icc 1 n, (n + 1 - i) * padicValNat p i := by
    congr! 1 with i i_in
    rw [padicValNat.pow (hp := Fact.mk prime_p)]
    · intro i_eq
      subst i
      simp at i_in
  rw [this]
  replace : ∑ i ∈ Finset.Icc 1 n, (n + 1 - i) * padicValNat p i =
    (∑ i ∈ Finset.Icc 1 n with p ∣ i, (n + 1 - i) * padicValNat p i) +
    (∑ i ∈ Finset.Icc 1 n with ¬ p ∣ i, (n + 1 - i) * padicValNat p i) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) (Dvd.dvd p)
      fun x ↦ (n + 1 - x) * padicValNat p x
  rw [this]
  replace : ∑ i ∈ Finset.Icc 1 n with ¬p ∣ i,
      (n + 1 - i) * padicValNat p i = 0 := by
    simp
    intro i i_ge i_le not_dvd
    simp [not_dvd]
  simp [this]
  clear this
  have pos_p : 0 < p := by exact Nat.Prime.pos prime_p

  have filter_dvd_eq_mul : (Finset.Icc 1 n).filter (λ i => p ∣ i)
    = (Finset.Icc 1 k).image (· * p) := by
    ext i
    simp
    constructor
    · rintro ⟨ ⟨i_ge_1, i_le_n⟩, p_dvd_i ⟩
      use i / p
      field_simp [and_comm, mul_comm]
      constructor <;> try constructor
      · exact Nat.mul_div_cancel' p_dvd_i
      · suffices i ≤ k * p by
          replace : i / p ≤ k * p / p := by gcongr
          convert this
          field_simp [prime_p.pos]
        by_contra! h
        obtain ⟨ j, j_eq ⟩ := p_dvd_i
        subst i
        rw [mul_comm] at h

        replace h : n / p < j := by
          simp at k_max
          specialize k_max j (by exact (Nat.mul_lt_mul_left pos_p).mp h)
          exact (Nat.div_lt_iff_lt_mul pos_p).mpr k_max

        have : p * j / p ≤ n / p := by
          exact Nat.div_le_div_right i_le_n
        field_simp [prime_p.pos] at this
        linarith

      · suffices 0 < i / p from this
        exact (Nat.lt_div_iff_mul_lt' p_dvd_i 0).mpr i_ge_1

    · rintro ⟨j, ⟨j_ge_1, j_le_k⟩, j_eq ⟩
      subst j_eq
      simp_all
      cases k_eq
      all_goals
        subst k
        specialize k_max 4
        interval_cases j <;> omega

  have : ∑ i ∈ Finset.Icc 1 n with p ∣ i, (n + 1 - i) * padicValNat p i  =
      ∑ i ∈ Finset.Icc 1 n with p ∣ i, (n + 1 - i) := by
    congr! 1 with i i_in
    simp at i_in
    have : 0 < padicValNat p i := by
      have := i_in.right
      have := Fact.mk prime_p
      rw [dvd_iff_padicValNat_ne_zero (by linarith)] at i_in
      suffices padicValNat p i ≠ 0 by
        exact Nat.zero_lt_of_ne_zero this

      simp [i_in]

    have : n < p^2 := by
      simp_all
      specialize k_max 4 (by omega)
      have p_gt_4 : 4 < p := by omega
      have : 16 < p^2 := by
        apply Nat.sqrt_lt'.mp
        rw [show 16 = 4^2 by rfl]
        rw [Nat.sqrt_eq' 4]
        exact p_gt_4

      rw [show 16 = 4*4 by rfl] at n_gt this
      have : 4 * p < p ^ 2 := by
        rw [sq]
        gcongr

      exact Nat.lt_of_le_of_lt k_max.le this

    suffices padicValNat p i = 1 by simp_all
    obtain ⟨ ⟨i_ge, i_le⟩, p_dvd_i ⟩ := i_in
    exact vp1 n p i this p_dvd_i i_le i_ge prime_p

  simp_all
  rw [Finset.sum_image]

  intro x x_in y y_in eq
  have : p ≠ 0 := prime_p.ne_zero
  exact (Nat.mul_left_inj this).mp eq


lemma no_circle_arrangement {n} (n_gt_16 : 16 < n) (four_dvd : 4 ∣ n) :
  ¬ ∃ (a : ℕ → ℕ), (∀ i, a i ≠ 0) ∧ a n = a 0 ∧
    ∏ i ∈ Finset.range n, a i * a (i + 1) =
    ∏ i ∈ Finset.range n, (i + 1).factorial
    := by
  rintro ⟨a, pos_a, a_circle, prod_eq⟩
  have pos_n : 0 < n := by positivity
  have sq_eq : ∏ i ∈ Finset.range n, a i * a (i + 1)
      = (∏ i ∈ Finset.range n, a i) ^ 2 := by
    rw [Finset.prod_mul_distrib]
    have image_eq_offset : (Finset.range (n + 1)).image a
      = (Finset.range (n)).image λ i => a (i + 1) := by
      ext x
      simp
      constructor
      · rintro ⟨ y, y_in, y_eq ⟩
        by_cases h : y = 0
        · use n - 1
          constructor
          · simp
            exact pos_n
          · rw [Nat.sub_add_cancel pos_n]
            rw [a_circle]
            convert y_eq
            exact h.symm
        · use y - 1
          simp_all
          constructor
          · omega
          · rw [Nat.sub_add_cancel (by omega)]
            exact y_eq

      · rintro ⟨ y, y_in, y_eq ⟩
        use y + 1
        simp_all

    have an_ne_0 : a n ≠ 0 := pos_a n
    have : a 0 * ∏ i ∈ Finset.range n, a (i + 1) =
      ∏ i ∈ Finset.range (n+1), a i
      := by
      rw [(Nat.sub_eq_iff_eq_add pos_n).mp rfl]
      rw [Finset.prod_range_succ]
      simp [Nat.sub_add_cancel pos_n]
      have := Finset.prod_Ico_eq_prod_range a 1 n
      conv_rhs at this =>
        rhs; intro x; rw [add_comm]

      rw [<- this]
      rw [Finset.prod_range_succ]
      simp [<- mul_assoc, an_ne_0]
      rw [Finset.range_eq_Ico]
      rw [Finset.prod_eq_prod_Ico_succ_bot pos_n a]

    have succ_eq_offset : ∏ i ∈ Finset.range n, a (i + 1) =
      ∏ i ∈ Finset.range n, a i := by
      rw [Finset.prod_range_succ] at this
      simp [a_circle, mul_comm (a 0), pos_a 0] at this
      exact this

    rw [succ_eq_offset]
    exact Eq.symm (Nat.pow_two (∏ i ∈ Finset.range n, a i))

  rcases Nat.bertrand (n / 4) (by omega)
    with ⟨p, prime_p, n_lt_p, p_le_2n⟩

  obtain ⟨ k, k_eq_or, kp_lt, k_max ⟩ : ∃ k,
    (k = 2 ∨ k = 3) ∧
    k * p < n ∧
    ¬∃ j, j > k ∧ j * p ≤ n
     := by

    have n_ge_2p : 2 * p ≤ n := by omega
    have n_lt_4p : n < 4 * p := by omega

    by_cases p_lt_n3 : 3 * p ≤ n
    · use 3
      simp
      split_ands
      · suffices 3 * p ≠ n by omega
        intro eq
        subst eq
        have : Nat.Coprime 4 3 := by rfl
        have four_dvd : 4 ∣ p := by
          exact Nat.Coprime.dvd_of_dvd_mul_left this four_dvd

        have := Nat.not_prime_iff_exists_dvd_lt (by omega : 2 ≤ p)
        simp [prime_p] at this
        specialize this 4 four_dvd (by simp)
        suffices 4 ≠ p by omega
        intro eq
        subst p
        rw [show 4 = 2 * 2 by rfl] at prime_p
        exact Nat.not_prime_mul (by simp) (by simp) prime_p

      · intro j j_gt
        suffices n < 4 * p by
          exact lt_mul_of_lt_mul_right n_lt_4p j_gt
        exact n_lt_4p
    · use 2
      simp
      simp at p_lt_n3
      split_ands
      · simp_all
        suffices 2 * p ≠ n by omega
        intro eq
        subst eq
        simp_all
        have : p = 2 := by
          rw [show 4 = 2 * 2 by rfl] at four_dvd
          have : 2 ∣ p := by omega
          replace : Even p := by exact (even_iff_exists_two_nsmul p).mpr this
          rwa [Nat.Prime.even_iff prime_p] at this

        subst p
        omega

      · intro j j_lt
        suffices n ≤ 3 * p by
          exact lt_mul_of_lt_mul_right p_lt_n3 j_lt

        omega


  replace kp_lt : k * p < n := by
    have : k * p ≠ n := by
      intro kp_eq
      subst kp_eq
      have : p ≠ 2 := by omega
      have : ¬2 ∣ p := by
        intro dvd
        have odd := Nat.Prime.odd_of_ne_two prime_p this
        have even : Even p := by
          exact (even_iff_exists_two_nsmul p).mpr dvd
        rw [<- Nat.not_odd_iff_even] at even
        exact even odd
      cases k_eq_or
      · subst k
        simp_all
      · subst k
        have : 4 ∣ 3 ∨ 4 ∣ p := by
          omega
        simp [show 4 = 2 * 2 by rfl] at this
        omega

    exact kp_lt


  replace p_le_2n : p ≤ n / 2 := by omega

  have prod_eq_sum := v_p_factorial_eq_sum p k n
    prime_p k_eq_or kp_lt n_gt_16 k_max

  have even_padic : Even (padicValNat p ((∏ i ∈ Finset.range n, a i)^2)) := by
    have := padicValNat.pow 2
      (hp := by exact { out := prime_p })
      (show (∏ i ∈ Finset.range n, a i) ≠ 0 by
        exact Finset.prod_ne_zero_iff.mpr fun a a_1 ↦ pos_a a
      )

    simp [this]

  simp only [Finset.prod_Ico_eq_prod_range Nat.factorial,
    add_tsub_cancel_right, add_comm
  ] at prod_eq_sum

  rw [<- sq_eq, prod_eq, prod_eq_sum] at even_padic
  clear prod_eq sq_eq

  have odd_padic : Odd (∑ i ∈ Finset.Icc 1 k, (n + 1 - i * p)) := by
    rw [show ∑ i ∈ Finset.Icc 1 k, (n + 1 - i * p) =
      ∑ i ∈ Finset.Ico 1 (k+1), (n + 1 - i * p) by rfl
    ]
    rw [Finset.sum_Ico_eq_sum_range]
    simp
    rw [Finset.sum_tsub_distrib]
    case hfg =>
      intro x x_in
      simp at x_in
      have : x ≤ 2 := by omega
      interval_cases x
      · omega
      · omega
      · have : 3 * p < n := by exact mul_lt_of_mul_lt_right kp_lt x_in
        omega
    cases k_eq_or
    · simp_all
      simp [show Finset.range 2 = {0, 1} by rfl]
      ring_nf
      have even : Even (2 + n * 2) := by
        refine Nat.even_add.mpr (by simp)
      have odd : Odd (p * 3) := by
        rw [Nat.odd_mul]
        constructor
        · have : p ≠ 2 := by omega
          exact Nat.Prime.odd_of_ne_two prime_p this
        · exact Nat.odd_iff.mpr rfl

      have le : p * 3 ≤ 2 + n * 2 := by omega
      exact Nat.Even.sub_odd le even odd

    · simp_all
      simp [show Finset.range 3 = {0, 1, 2} by rfl]
      ring_nf
      have odd_3 : Odd 3 := by exact Nat.odd_iff.mpr rfl
      have odd : Odd (3 + n * 3) := by
        suffices Even (n * 3) by exact Even.odd_add this odd_3
        suffices Even n by exact Even.mul_right this 3
        have : 2 ∣ n := by omega
        exact (even_iff_exists_two_nsmul n).mpr this
      have even : Even (p * 6) := by
        suffices Even 6 by exact Even.mul_left this p
        rw [show 6 = 2 * 3 by rfl]
        exact Nat.even_mul_succ_self 2

      have le : p * 6 ≤ 3 + n * 3:= by omega
      exact Nat.Odd.sub_even le odd even

  rw [<- Nat.not_odd_iff_even] at even_padic

  exact even_padic odd_padic

theorem number_theory_604639
  : ¬ ∃ (a : ℕ → ℕ), (∀ i, a i ≠ 0) ∧ a 2024 = a 0 ∧
    ∏ i ∈ Finset.range 2024, a i * a (i + 1) =
    ∏ i ∈ Finset.range 2024, (i + 1).factorial
    := by
  exact no_circle_arrangement (by linarith : 16 < 2024) (by norm_num)
