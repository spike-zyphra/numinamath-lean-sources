import Mathlib

/-- How many positive perfect squares less than 10^6 are multiples of 24? -/
theorem number_theory_93335 :
    Set.ncard {n : ℕ | n > 0 ∧ ∃ k, n = k^2 ∧ 24 ∣ n ∧ n < 10^6} = 83 := by
  -- The prime factorization of 24 is 2^3 * 3.
  have equiv (n) : (∃ k, n = k^2 ∧ 24 ∣ n) ↔ ∃ k, n = (12 * k)^2 := by
    constructor
    · rintro ⟨k, rfl, div⟩
      have pr2 : Nat.Prime 2 := by norm_num
      have pr3 : Nat.Prime 3 := by norm_num
      -- Thus each square must have at least one factor of 3,
      have : 3 ∣ k^2 := by trans 24; norm_num; exact div
      obtain ⟨k', rfl⟩ : 3 ∣ k := pr3.dvd_of_dvd_pow this
      rw[mul_pow] at div
      change 3 * 2^3 ∣ 3^2 * k' ^2 at div
      -- and at least 3 factors of 2.
      have : 2 ^ 3 ∣ 3 ^ 2 * k' ^ 2 := dvd_of_mul_left_dvd div
      have div8 := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this
      have : 2 ^ 2 ∣ k' ^ 2 := by trans 2 ^ 3; norm_num; assumption
      obtain ⟨k'', eq⟩ : 2 ∣ k' := by rwa[Nat.pow_dvd_pow_iff (by simp)] at this
      rw[eq, mul_pow] at div8
      -- Hence its square root must have 2 factors of 2 and 1 factors of 3.
      change 4 * 2 ∣ 4 * k'' ^ 2 at div8
      rw[Nat.mul_dvd_mul_iff_left (by simp)] at div8
      have := pr2.dvd_of_dvd_pow div8
      obtain ⟨k''', eq'⟩ := this
      exists k'''
      -- This means that each such square is in the form (12c)^2, where 0 < 12c < 10^3 is a positive integer.
      rw[mul_pow, eq, mul_pow, eq']
      ring
    · rintro ⟨k,rfl⟩
      exists 12 * k
      simp only [mul_pow, Nat.reducePow, true_and]
      trans 144
      · norm_num
      · apply Nat.dvd_mul_right

  -- This holds for all the 0 < c < 83.
  have (n) : (n > 0 ∧ ∃ k, n = k ^ 2 ∧ 24 ∣ n ∧ n < 10 ^ 6) ↔ ∃ k, k > 0 ∧ k < 84 ∧ n = (12 * k)^2 := by
    constructor
    · rintro ⟨pos, k,eq, div, lt⟩
      have : ∃ k, n = k^2 ∧ 24 ∣ n := ⟨k, eq, div⟩
      rw[equiv] at this
      obtain ⟨k,rfl,div⟩ := this
      change (12 * k)^2 < 10^(3 * 2) at lt
      rw[pow_mul, Nat.pow_lt_pow_iff_left (by simp)] at lt
      exists k
      split_ands
      · rw[mul_pow] at pos
        replace pos := Nat.pow_pos_iff.mp $ Nat.pos_of_mul_pos_left pos
        simpa using pos
      · change k < 1008 / 12
        rw[Nat.lt_div_iff_mul_lt' (by norm_num)]
        trans 10^3
        · assumption
        · norm_num
      · rfl
    · rintro ⟨k,gt,lt, rfl⟩
      constructor
      · simp[gt]
      · exists 12 * k
        split_ands
        · rfl
        · rw[mul_pow]
          trans 144
          · norm_num
          · apply Nat.dvd_mul_right
        · change (12 * k)^2 < 10^(3 * 2)
          rw[pow_mul, Nat.pow_lt_pow_iff_left (by simp)]
          linarith
  -- Hence the set in question is the image of f(x) = (12x)^2 on the integer interval (0,84).
  have : {n : ℕ | n > 0 ∧ ∃ k, n = k^2 ∧ 24 ∣ n ∧ n < 10^6} = (fun x => (12 * x)^2) '' Set.Ioo 0 84 := by
    ext n
    rw[Set.mem_setOf, this, Set.mem_image]
    apply exists_congr
    intro a
    rw[Set.mem_Ioo]
    tauto
  rw[this]
  -- The latter has cardinality 83,
  have : (Set.Ioo 0 84).ncard = 83 := by
    change (Set.Ioo 0 84).ncard = 84 - 0 - 1
    rw[← Set.Nat.card_coe_set_eq]
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Nat.card_Ioo, tsub_zero,
      Nat.add_one_sub_one]
  -- and the function is injective on that interval, hence the set also has cardinality 83.
  rwa[Set.ncard_image_of_injOn]
  · intro x hx y hy eq
    simpa using eq