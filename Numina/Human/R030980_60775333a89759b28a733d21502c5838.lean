import Mathlib

/- Find the number of rational numbers $r$, $0 < r < 1$, such that when $r$ is written as a fraction in lowest terms, the numerator and the denominator have a sum of 1000. -/
theorem number_theory_95900 :
    Set.ncard {r : ℚ | 0 < r ∧ r < 1 ∧ r.num + r.den = 1000} = 200 := by

  -- First, let's rewrite the set in a more convenient form by splitting out the numerator and denominator.
  let f1 : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have f1_inj : Function.Injective f1 := by
    intro r1 r2
    simp [f1]
    exact Rat.ext
  have f1_image : f1 '' {r : ℚ | 0 < r ∧ r < 1 ∧ r.num + r.den = 1000} = {(x, y) : ℤ × ℕ | 0 < x ∧ x < y ∧ x + y = 1000 ∧ Nat.Coprime (Int.natAbs x) y} := by
    ext ⟨n, d⟩
    simp
    constructor
    . rintro ⟨r, ⟨h1, h2, h3⟩, h4⟩
      simp [f1] at h4
      obtain ⟨hr1, hr2⟩ := h4
      rw [← hr1, ← hr2]
      and_intros
      any_goals simpa
      . qify
        rw [← div_lt_one (by simp [Rat.den_pos])]
        simpa [Rat.num_div_den r]
      . exact Rat.reduced r
    . rintro ⟨h1, h2, h3, h4⟩
      use Rat.mk' n d (by linarith) h4
      simp [f1, h3]
      and_intros
      . rw [← Rat.num_pos]
        simpa
      . rw [Rat.mk_eq_mkRat, Rat.mkRat_eq_div, div_lt_one (by norm_cast; linarith)]
        norm_cast
  rw [← Set.ncard_image_of_injective _ f1_inj, f1_image]

  -- Next, we can substitute in for y = 1000 - x. Note that gcd(x, 1000 - x) = gcd(x, 1000).
  let f2 : ℕ → ℤ × ℕ := fun x => (x, 1000 - x)
  have f2_inj : Function.Injective f2 := by
    rintro x1 x2
    simp [f2]
    intro h _
    exact h
  have f2_image : f2 '' ↑{x ∈ Finset.Ioo 0 500 | Nat.Coprime x 1000} = {(x, y) : ℤ × ℕ | 0 < x ∧ x < y ∧ x + y = 1000 ∧ Nat.Coprime (Int.natAbs x) y} := by
    ext ⟨x, y⟩
    simp [f2]
    constructor
    . rintro ⟨x', ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩⟩
      rw [← h4, ← h5, Int.ofNat_sub (show x' ≤ 1000 by linarith)]
      simp
      zify at h1 h2
      and_intros
      . linarith
      . rw [lt_tsub_iff_right]
        linarith
      . rw [Nat.Coprime, Nat.gcd_sub_self_right (show x' ≤ 1000 by linarith), h3]
    . rintro ⟨h1, h2, h3, h4⟩
      have : 0 ≤ x := by linarith
      use Int.natAbs x
      and_intros
      all_goals zify
      . rw [abs_of_pos h1]
        exact h1
      . rw [abs_of_pos h1]
        linarith
      . rw [show 1000 = Int.natAbs x + y by zify; rw [abs_of_pos h1, h3]]
        simpa
      . exact abs_of_pos h1
      . rw [Int.ofNat_sub (show (Int.natAbs x) ≤ 1000 by zify; rw [abs_of_pos h1]; linarith)]
        simp
        rw [abs_of_pos h1]
        linarith
  rw [← f2_image, Set.ncard_image_of_injective _ f2_inj, Set.ncard_coe_Finset]

  -- Next we need to count the elements of this set. We can show that the number of integers coprime to 1000 in (0, 500)
  -- is the same as the number in (500, 1000) via the bijection x ↦ 1000 - x.
  have reflect_range : {x ∈ Finset.Ioo 0 500 | Nat.Coprime x 1000}.card = {x ∈ Finset.Ioo 500 1000 | Nat.Coprime x 1000}.card := by
    let f : ℕ → ℕ := fun x => 1000 - x
    have f_inj : Set.InjOn f {x ∈ Finset.Ioo 0 500 | Nat.Coprime x 1000} := by
      simp [f]
      intro x1 ⟨⟨_, _⟩, _⟩ x2 ⟨⟨_, _⟩, _⟩
      zify
      rw [Int.ofNat_sub (show x1 ≤ 1000 by linarith)]
      rw [Int.ofNat_sub (show x2 ≤ 1000 by linarith)]
      simp
    have f_image : f '' {x ∈ Finset.Ioo 0 500 | Nat.Coprime x 1000} = {x ∈ Finset.Ioo 500 1000 | Nat.Coprime x 1000} := by
      ext x
      simp [f]
      constructor
      . rintro ⟨x', ⟨⟨_, _⟩, h⟩, hx⟩
        and_intros
        . omega
        . omega
        . rw [← hx, Nat.Coprime, Nat.gcd_self_sub_left (show x' ≤ 1000 by linarith), h]
      . rintro ⟨⟨_, _⟩, h⟩
        use 1000 - x
        and_intros
        . omega
        . omega
        . rw [Nat.Coprime, Nat.gcd_self_sub_left (show x ≤ 1000 by linarith), h]
        . omega
    rw [← Set.ncard_coe_Finset, ← Set.ncard_coe_Finset, ← f_image, Set.ncard_image_of_injOn f_inj]
    simp

  -- 0 and 500 are obviously not coprime to 1000, so our answer is one-half the number of integers coprime to 1000 in (0, 1000),
  -- which we can compute using the totient function.
  suffices : {x ∈ Finset.range 1000 | Nat.Coprime x 1000}.card = 400
  . have eq : {x ∈ Finset.range 1000 | Nat.Coprime x 1000}.card = {x ∈ Finset.Ioo 0 500 | Nat.Coprime x 1000}.card * 2 := by
      rw [Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (show 0 ≤ 500 by norm_num) (show 500 ≤ 1000 by norm_num),
        Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
        ← Finset.Ioo_insert_left (show 0 < 500 by norm_num), ← Finset.Ioo_insert_left (show 500 < 1000 by norm_num),
        Finset.filter_insert, Finset.filter_insert]
      simp [show ¬(Nat.Coprime 0 1000) by norm_num, show ¬(Nat.Coprime 500 1000) by norm_num]
      rw [reflect_range, mul_two]
    rw [this] at eq
    linarith
  rw [Finset.filter_congr (fun x _ => Nat.coprime_comm), ← Nat.totient_eq_card_coprime]

  -- Finally, we use 1000 = 2^3 * 5^3 to compute the totient function.
  rw [show 1000 = 2^3 * 5^3 by norm_num, Nat.totient_mul (show Nat.Coprime (2 ^ 3) (5 ^ 3) by norm_num),
    Nat.totient_prime_pow (show Nat.Prime 2 by norm_num) (show 0 < 3 by norm_num),
    Nat.totient_prime_pow (show Nat.Prime 5 by norm_num) (show 0 < 3 by norm_num)]
  simp