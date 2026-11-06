import Mathlib



/- 4. Determine the number of all triples of natural numbers $a, b, c$, for which
$$
a + ab + abc + ac + c = 2017 \text{.}
$$ -/
theorem number_theory_266812:
  {(a,b,c): ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
    a+a*b+a*b*c + a*c + c = 2017}.ncard = 29 := by

  -- simplify the equation
  have {a b c: ℕ}: a+a*b+a*b*c + a*c + c = 2017 ↔
    (1+c)*(a*(1+b)+1) = 2018 := by
    zify
    constructor <;> intro h <;> linarith only [h]

  -- if a x b = 2018 = 2 x 1009, then a = 1 or 2 or 1009 or 2018.
  have eq_or {a b: ℕ} (p q: ℕ) (hpq: p ≠ q) (pp: Nat.Prime p) (pq: Nat.Prime q)
    (heq: a * b = p*q): a = 1 ∨ a = p ∨ a = q ∨ a = p*q := by
    have advd: a ∣ p*q := by
      use b
      rw [heq]
    by_cases ha: p ∣ a
    · rcases ha with ⟨d, hd⟩
      rw [hd] at advd
      replace advd: d ∣ q := Nat.dvd_of_mul_dvd_mul_left pp.pos advd
      rw [Nat.dvd_prime pq] at advd
      rcases advd with (rfl | rfl)
      <;> simp [hd]
    · simp only [pp.dvd_iff_not_coprime, Decidable.not_not] at ha
      have: a ∣ q := by
        rw [Nat.coprime_comm] at ha
        exact ha.dvd_of_dvd_mul_left advd
      rw [Nat.dvd_prime pq] at this
      clear * - this
      tauto

  -- if we require a,b,c > 0, then 1+c ≥ 2, a(1+b) + 1 > 3.
  -- only possible case is 1+c = 2 and a(1+b)+1 = 1009
  replace {a b c: ℕ}: (0 < a ∧ 0 < b ∧ 0 < c ∧
    a+a*b+a*b*c + a*c + c = 2017) ↔
    (0 < a ∧ 0 < b ∧ c = 1 ∧ a*(1+b)+1 = 1009) := by
    rw [this]
    simp only [and_congr_right_iff]
    intro apos bpos
    constructor
    · rintro ⟨cpos, heq⟩
      replace: 2018 = 2 * 1009 := by norm_num
      rw [this] at heq
      specialize eq_or 2 1009 (by norm_num) (by norm_num) (by norm_num) heq
      rcases eq_or with eq1 | eq2 | eq3 | eq4
      · have: c = 0 := Nat.self_eq_add_right.mp eq1.symm
        simp [this] at cpos
      · have ceq: c = 1 := by linarith only [eq2]
        rw [eq2] at heq
        refine ⟨ceq, ?_⟩
        apply Nat.eq_of_mul_eq_mul_left (by norm_num) heq
      · rw [eq3, mul_comm 2 1009] at heq
        replace heq := Nat.eq_of_mul_eq_mul_left (by norm_num) heq
        replace heq: a * (1+b) = 1 := by linarith only [heq]
        have h1: a ≥ 1 := by exact apos
        have h2: 1+b ≥ 2 := by omega
        have h3: a * (1+b) ≥ 1*2 := Nat.mul_le_mul apos h2
        norm_num [heq] at h3
      · simp only [eq4, Nat.reduceMul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀,
        add_left_eq_self, mul_eq_zero, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, false_and,
        or_false] at heq
        simp [heq] at apos
    · rintro ⟨ceq, heq⟩
      norm_num [ceq, heq]

  -- and that simplifies to a(1+b) = 1008
  replace: {(a,b,c): ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
    a+a*b+a*b*c + a*c + c = 2017}.ncard = {b': ℕ |
    2 ≤ b' ∧ b' ≤ 1008 ∧ b' ∣ 1008}.ncard := by
    set s := {(a,b,c): ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
    a+a*b+a*b*c + a*c + c = 2017} with s_def
    let f: (x:ℕ × ℕ × ℕ) → (hh: x ∈ s) → ℕ := fun x hh => x.2.1 + 1
    apply Set.ncard_congr f
    · rintro ⟨a,b,c⟩ h
      simp only [Set.mem_setOf_eq, Nat.reduceLeDiff, s, f]
      simp only [s_def, Set.mem_setOf_eq] at h
      rw [this] at h
      have bpos := h.right.left
      have heq: a*(1+b) = 1008 := by
        linarith only [h.right.right.right]
      split_ands
      · exact bpos
      · have: 1 + b ∣ 1008 := by
          rw [← heq]
          apply Nat.dvd_mul_left
        replace := Nat.le_of_dvd (by norm_num) this
        linarith only [this]
      · rw [← heq, add_comm b 1]
        apply Nat.dvd_mul_left
    · rintro ⟨a1,b1,c1⟩ ⟨a2,b2,c2⟩ hh1 hh2
      simp only [add_left_inj, Prod.mk.injEq, f, s]
      intro beq
      simp only [Set.mem_setOf_eq, s, f] at hh1 hh2
      rw [this] at hh1 hh2
      refine ⟨?_, beq, ?_⟩
      · have: a1 * (1 + b1) = a2 * (1 + b2) := by
          simp only [Nat.reduceEqDiff, s, f] at hh1 hh2
          rw [hh1.right.right.right, ← hh2.right.right.right]
        rw [beq] at this
        apply Nat.eq_of_mul_eq_mul_right ?_ this
        simp
      · rw [hh1.right.right.left, hh2.right.right.left]
    · intro b
      simp only [Set.mem_setOf_eq, Prod.exists, and_imp, s, f]
      intro bge ble bdvd
      rcases bdvd with ⟨a, heq⟩
      have hb: b = (b-1) + 1 := by omega
      replace heq: a * (b-1 + 1) + 1 = 1009 := by
        rw [← hb, mul_comm a b, ← heq]
      use a,(b-1),1
      refine exists_prop.mpr ?_
      rw [← hb, this, ← heq, add_comm (b-1) 1]
      simp only [tsub_pos_iff_lt, and_self, and_true, s, f]
      constructor
      · by_contra!
        replace: a = 0 := Nat.eq_zero_of_le_zero this
        simp [this] at heq
      · linarith only [bge]
  rw [this]

  -- then it suffices to consider divisors of 1008
  replace: {b': ℕ |
    2 ≤ b' ∧ b' ≤ 1008 ∧ b' ∣ 1008} = (Nat.divisors 1008).erase 1 := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_erase, Set.mem_diff, Finset.mem_coe,
    Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    and_true, Set.mem_singleton_iff]
    constructor
    · intro h; simp only [h, true_and]
      apply ne_of_gt; exact h.left
    · rintro ⟨ndvd, hn⟩
      split_ands
      · have: n ≠ 0 := by
          rintro rfl
          norm_num at ndvd
        omega
      · apply Nat.le_of_dvd (by norm_num) ndvd
      · exact ndvd
  rw [this, Set.ncard_coe_Finset, Finset.card_erase_of_mem (by simp)]


  -- 1008 = 2^4 x 3^2 x 7.
  -- so number of divisors of 1008 is (4+1) x (2+1) x (1+1) = 30
  -- and if we do not count 1, result is 29.
  have: (1008:ℕ) = 2^4 * 3^2 * 7 := by norm_num
  rw [this, ← ArithmeticFunction.sigma_zero_apply]
  replace := @ArithmeticFunction.isMultiplicative_sigma 0
  rw [ArithmeticFunction.IsMultiplicative] at this
  have co1: Nat.Coprime (2^4 * 3^2) 7 := by
    norm_num
  have co2: Nat.Coprime (2^4) (3^2) := by norm_num
  rw [this.right co1, this.right co2,
  ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num),
  ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num),
  ← pow_one 7, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num)]
  norm_num