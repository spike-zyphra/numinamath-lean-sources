import Mathlib

open Finset

namespace number_theory_24031

/- nth_bit x n is the n-th bit of the decimal expansion of x -/
noncomputable def nth_bit (x : ℝ) (n : ℕ) : ℕ := ⌊x * 10 ^ n⌋₊ % 10

/- nth_residual a b n is the n-th residual of a * 10 % b -/
noncomputable def nth_residual (a b : ℕ) (n : ℕ) := Nat.repeat (fun x => x * 10 % b) n (a % b)

end number_theory_24031

open number_theory_24031

/- nth_residual a b 0 = a % b -/
lemma nth_residual_zero {a b : ℕ} : nth_residual a b 0 = a % b := by rfl

/- nth_residual a b (k + 1) = (nth_residual a b k) * 10 % b -/
lemma nth_residual_succ {a b k : ℕ} : nth_residual a b (k + 1) = (nth_residual a b k) * 10 % b := by rfl

/- nth_residual a b (k + 1) = nth_residual (a * 10) b k -/
lemma nth_residual_succ' {a b k : ℕ} : nth_residual a b (k + 1) = nth_residual (a * 10) b k := by
  induction k with
  | zero =>
    simp [nth_residual_succ, nth_residual_zero]
  | succ k ih =>
    rw [nth_residual_succ, ih, nth_residual_succ]

/- nth_bit (a / b) 0 = (a / b) % 10 -/
lemma nth_bit_zero {a b : ℕ} : nth_bit (a / b : ℝ) 0 = (a / b) % 10 := by
  simp [nth_bit]
  congr
  exact Nat.floor_div_eq_div a b

/- nth_bit (a / b) (n + 1) = nth_bit (x * 10) n-/
lemma nth_bit_succ {x : ℝ} (n : ℕ) : nth_bit x (n + 1) = nth_bit (x * 10) n := by
  simp [nth_bit]
  congr 2
  ring

/- nth_bit (a / b : ℝ) (k + 1) = (nth_residual a b k) * 10 / b -/
lemma nth_bit_eq_residual {a b k : ℕ} : nth_bit (a / b : ℝ) (k + 1) = (nth_residual a b k) * 10 / b := by
  induction k generalizing a with
  | zero =>
    simp [nth_residual_zero, nth_bit_succ]
    have : a / b * 10 = (a * 10 : ℕ) / (b : ℝ) := by simp; ring
    rw [this, nth_bit_zero]
    rw [←Nat.mod_mul_right_div_self, Nat.mul_mod_mul_right]
  | succ k ih =>
    rw [nth_bit_succ, nth_residual_succ']
    have : a / b * 10 = (a * 10 : ℕ) / (b : ℝ) := by simp; ring
    rw [this, ih]

/- We prove that nth_residual a b are not pair-wise distinct -/
lemma exists_periodic_residual {a b : ℕ} (hb : b > 0) : ∃ n > 0, ∃ k, nth_residual a b (k + n) = nth_residual a b k := by
  let s := range (b + 1)
  let t := range b
  -- Note that nth_residual a b k < b for all k.
  -- Apply the pigeonhole principle to obtain the result.
  have hf : ∀ k ∈ s, nth_residual a b k ∈ t := by
    intro k _
    induction k with
    | zero =>
      simp [nth_residual_zero, t]
      exact Nat.mod_lt a hb
    | succ k ih =>
      simp [nth_residual_succ, t]
      exact Nat.mod_lt (nth_residual a b k * 10) hb
  have hcard : #t * 1 < #s := by simp [s, t]
  obtain ⟨y, hmem, hy⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hcard
  obtain ⟨a, ha, b, hb, hne⟩ := one_lt_card.mp hy
  wlog hab : a < b generalizing a b with H
  · simp at hab
    apply H b hb a ha
    · exact id (Ne.symm hne)
    · exact Nat.lt_of_le_of_ne hab (id (Ne.symm hne))
  · use b - a
    constructor
    · exact Nat.zero_lt_sub_of_lt hab
    · use a
      rw [Nat.add_sub_cancel']
      · simp at ha hb
        simp [ha.2, hb.2]
      · exact Nat.le_of_succ_le hab

/- We prove that nth_residual a b is periodic. -/
lemma periodic_residual {a b : ℕ} (hb : b > 0) : ∃ n > 0, ∃ m, ∀ k ≥ m, nth_residual a b (k + n) = nth_residual a b k := by
  -- Since nth_residual a b is not distinct, we can find n and k such that nth_residual a b (k + n) = nth_residual a b k.
  -- Then k is the first index where the periodicity starts and n is the period.
  obtain ⟨n, hn, k, hk⟩ := exists_periodic_residual (a := a) hb
  use n, hn, k
  intro m hm
  induction m, hm using Nat.le_induction
  case base =>
    exact hk
  case succ =>
    rename_i m hm ih
    have : m + 1 + n = m + n + 1 := by ring
    simp [this, nth_residual_succ, ih]

/- We prove that nth_bit (a / b) is eventually periodic. -/
lemma periodic_bit {a b : ℕ} (hb : b > 0) : ∃ n > 0, ∃ m, ∀ k ≥ m, ∀ r, nth_bit (a / b) (k + r * n) = nth_bit (a / b) k := by
  obtain ⟨n, hn, m, hm⟩ := periodic_residual (a := a) hb
  use n, hn, m + 1
  intro k hk r
  induction r generalizing k with
  | zero =>
    simp
  | succ r ih =>
    have : k + (r + 1) * n = k + n + r * n := by ring
    rw [this, ih _ (Nat.le_add_right_of_le hk)]
    have : k + n = k - 1 + n + 1 := by
      rw [add_assoc, add_comm n 1, ←add_assoc, Nat.sub_add_cancel]
      exact Nat.one_le_of_lt hk
    rw [this, nth_bit_eq_residual]
    have : k = k - 1 + 1 := by
      rw [Nat.sub_add_cancel]
      exact Nat.one_le_of_lt hk
    nth_rw 2 [this]
    rw [nth_bit_eq_residual]
    congr 2
    rw [hm]
    exact Nat.le_sub_one_of_lt hk

/- We prove that if x is rational, then the decimal expansion of x is eventually periodic. -/
lemma periodic_of_rational (x : ℚ) (hx : x > 0) : ∃ n > 0, ∃ m, ∀ k ≥ m, ∀ r, nth_bit x (k + r * n) = nth_bit x k := by
  -- Note that x = a / b for some a b.
  -- Then by lemma periodic_bit, we can find n and m such that nth_bit (a / b) is periodic.
  set a := x.num with ha
  set b := x.den with hb
  clear_value a b
  have hx_eq : x = a / b := by
    rw [ha, hb]
    exact Eq.symm (Rat.num_div_den x)
  have ha_pos : a > 0 := by
    rw [ha]
    exact Rat.num_pos.mpr hx
  lift a to ℕ using le_of_lt ha_pos
  norm_num at hx_eq
  simp [hx_eq]
  apply periodic_bit
  rw [hb]
  exact Rat.den_pos x

/- If there is a whole period such that the bits are all zeros, then all the bits are zero after this period. -/
lemma eventually_zero_of_periodic {x : ℚ} (hx : x > 0) :
    ∃ n > 0, ∃ M, ∀ m ≥ M, (∀ k ∈ Ico m (m + n), nth_bit x k = 0) → ∀ k ≥ m, nth_bit x k = 0 := by
  obtain ⟨n, hn, m, hm⟩ := periodic_of_rational x hx
  use n, hn, m
  intro M hM hzero k hk
  let r := (k - M) / n
  let l := M + (k - M) % n
  have hr : l + r * n = k := by
    simp [l, r, add_assoc]
    rw [Nat.mod_add_div', Nat.add_sub_cancel']
    exact hk
  rw [←hr, hm]
  · apply hzero
    simp [l]
    exact Nat.mod_lt (k - M) hn
  · simp [l]
    exact Nat.le_add_right_of_le hM

/- We prove that the a is well-defined. -/
lemma summable_a (n : ℕ) :
    Summable (fun i : ℕ => 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ)) := by
  have hx {x : ℕ} : x < 10 ^ (Nat.digits 10 x).length := by exact Nat.lt_base_pow_length_digits'
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => 10 ^ (- n : ℤ))
  · intro i
    positivity
  · intro i
    rw [←Nat.Icc_insert_succ_right]
    rw [sum_insert, Nat.cast_add, neg_add, add_comm, zpow_add₀]
    rw [mul_assoc]
    trans 10 ^ (-↑(∑ x ∈ Icc 1 i, (Nat.digits 10 (x ^ n)).length) : ℤ) * (10 ^ (-↑(Nat.digits 10 ((i + 1) ^ n)).length : ℤ) * 10 ^ (↑(Nat.digits 10 ((i + 1) ^ n)).length : ℤ))
    · gcongr
      norm_cast
      apply le_of_lt hx
    trans 10 ^ (-↑(∑ x ∈ Icc 1 i, (Nat.digits 10 (x ^ n)).length) : ℤ) * 1
    · gcongr
      apply le_of_eq
      rw [←zpow_add₀]
      · ring_nf
      · simp
    trans 10 ^ (-↑(∑ x ∈ Icc 1 i, 1 : ℤ))
    · rw [mul_one]
      gcongr
      · simp
      · norm_cast
        apply sum_le_sum
        intro i hi
        by_contra h
        simp at h
        apply Nat.digits_eq_nil_iff_eq_zero.mp at h
        simp at h hi
        simp [h.1] at hi
    all_goals simp
  · have : (fun n : ℕ ↦ (10 : ℝ) ^ (-↑n : ℤ)) = fun n : ℕ ↦ (10⁻¹ : ℝ) ^ n := by simp
    rw [this]
    refine summable_geometric_of_lt_one ?_ ?_
    all_goals norm_num

/- We prove that 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ) =
    (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ)  -/
lemma bit_a₀ {i t : ℕ} (hi : i < k) :
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ) =
    (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ)
     := by
  push_cast
  simp
  left
  rw [←zpow_natCast]
  congr 1
  push_cast
  have :  Icc 1 k = (Icc 1 (i + 1)) ∪ Ioc (i + 1) k := by
    ext j
    simp
    constructor <;> intro hj
    · by_cases hj' : j ≤ i + 1
      · simp [hj', hj.1]
      · simp [hj.2]
        simp at hj'
        simp [hj']
    · rcases hj with hj | hj
      · simp [hj.1]
        apply le_trans hj.2
        exact hi
      · simp [hj.2]
        apply le_trans ?_ hj.1
        simp
  simp [this]
  rw [sum_union]
  · ring
  · apply disjoint_left.mpr
    intro j hj
    simp at hj ⊢
    intro hj'
    have : ¬ i + 1 < j := by
      simp [hj]
    contradiction

/- We prove that 10 ∣ (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ) -/
lemma ten_dvd_mul (ht : t > 0) : 10 ∣ (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ) := by
  apply dvd_mul_of_dvd_left
  apply dvd_pow_self
  apply ne_of_gt
  apply add_pos_of_nonneg_of_pos
  · simp
  · exact ht

/- If  Int.fract a + Int.fract b < 1, a ≥ 0 and b ≥ 0, then ⌊a + b⌋₊ = ⌊a⌋₊ + ⌊b⌋₊ -/
lemma floor_add {a b : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hab : Int.fract a + Int.fract b < 1) : ⌊a + b⌋₊ = ⌊a⌋₊ + ⌊b⌋₊ := by
  trans ⌊⌊a⌋ + Int.fract a + b⌋₊
  · congr
    exact Eq.symm (Int.floor_add_fract a)
  trans ⌊⌊a⌋ + Int.fract a + (⌊b⌋ + Int.fract b)⌋₊
  · congr
    exact Eq.symm (Int.floor_add_fract b)
  trans ⌊Int.fract a + Int.fract b + (⌊a⌋ +  ⌊b⌋)⌋₊
  · ring_nf
  trans ⌊Int.fract a + Int.fract b + (⌊a⌋₊ +  ⌊b⌋₊)⌋₊
  · congr
    · exact Eq.symm (Int.natCast_floor_eq_floor ha)
    · exact Eq.symm (Int.natCast_floor_eq_floor hb)
  · rw [←Nat.cast_add]
    rw [Nat.floor_add_nat]
    simp
    · exact hab
    · apply add_nonneg
      · exact Int.fract_nonneg a
      · exact Int.fract_nonneg b

/- We prove that for any k, a can be expressed as three parts ∑ i ∈ range k, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ) +
        10 ^ (-∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ) +
        ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + k + 1 + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 1 + 1) ^ n : ℝ). -/
lemma a_eq (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ)) (k : ℕ) :
    a n = ∑ i ∈ range k, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ) +
        10 ^ (-∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ) +
        ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + k + 1 + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 1 + 1) ^ n : ℝ) := by
  -- We prove that ∑' i, a i = ∑ i ∈ range k, a i + a k + ∑' i, a (i + k + 1)
  have tsum_eq (a : ℕ → ℝ) (ha : Summable a) (k : ℕ) : ∑' i, a i = ∑ i ∈ range k, a i + a k + ∑' i, a (i + k + 1) := by
    induction k with
    | zero =>
      simp
      exact tsum_eq_zero_add ha
    | succ i ih =>
      rw [ih]
      nth_rw 2 [add_assoc]
      congr
      · exact Eq.symm (sum_range_succ a i)
      · rw [tsum_eq_zero_add]
        simp
        · apply tsum_congr
          ring_nf
          simp
        · simp [add_assoc]
          apply summable_nat_add_iff _ |>.mpr ha
  simp [ha]
  rw [tsum_eq _ ?_ k]
  · simp
  · obtain h := summable_a n
    simp at h
    exact h

/- We prove that for any k,  a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t) can be expressed as three parts
    ∑ i ∈ range k, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ) +
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ) +
    ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ)-/
lemma a_mul_pow (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ))
    {k n t : ℕ} : a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t) =
    ∑ i ∈ range k, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ) +
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ) +
    ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) := by
  rw [a_eq a ha k, add_mul, add_mul]
  congr 1
  · congr 1
    · rw [sum_mul]
      apply sum_congr rfl
      intro _ _
      nth_rw 2 [mul_comm]
      nth_rw 3 [mul_comm]
      rw [mul_assoc]
      congr
      rw [←zpow_natCast, ←zpow_add₀]
      · congr 1
        simp
        ring
      · simp
    · nth_rw 2 [mul_comm]
      nth_rw 3 [mul_comm]
      rw [mul_assoc]
      congr
      rw [←zpow_natCast, ←zpow_add₀]
      · congr 1
        simp
        ring
      · simp
  · rw [←tsum_mul_right]
    congr
    ext x
    nth_rw 2 [mul_comm]
    nth_rw 3 [mul_comm]
    rw [mul_assoc]
    congr 1
    · congr 1
      simp [add_assoc]
      ring
    rw [←zpow_natCast, ←zpow_add₀]
    · congr 1
      simp
      ring
    · simp

/- We prove that for any k, ⌊a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t)⌋₊ = ∑ i ∈ range k, (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ) +
    ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ) +
    ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ)⌋₊ -/
lemma floor_a_mul_pow (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ))
    {k n t : ℕ} :
    ⌊a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t)⌋₊ = ∑ i ∈ range k, (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ) +
    ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ) +
    ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ)⌋₊ := by
  rw [a_mul_pow a ha]
  nth_rw 8 [add_comm]
  rw [←Nat.floor_add_nat]
  congr 1
  nth_rw 8 [add_comm]
  rw [←add_assoc]
  congr
  · rw [Nat.cast_sum, Nat.cast_sum]
    apply sum_congr rfl
    intro i hi
    simp at hi
    obtain h := bit_a₀ (n := n) (t := t) hi
    push_cast at h ⊢
    rw [h]
  · apply add_nonneg
    · positivity
    · apply tsum_nonneg
      intro i
      positivity

/- We prove that if  ∃ k, (∃ t : ℕ, x * 10 ^ k = t) ∧ 1 > y * 10 ^ k and y ≥ 0, then  Int.fract x + Int.fract y = Int.fract (x + y) -/
lemma fract_add {x y : ℝ} (hy : y ≥ 0) (h : ∃ k, (∃ t : ℕ, x * 10 ^ k = t) ∧ 1 > y * 10 ^ k ) : Int.fract x + Int.fract y = Int.fract (x + y) := by
  obtain ⟨k, ⟨t, hk₁⟩, hk₂⟩ := h
  have hx : x = t / 10 ^ k := by
    rw [←hk₁]
    field_simp
  have ht : t = t / 10 ^ k * 10 ^ k + t % 10 ^ k := by exact Eq.symm (Nat.div_add_mod' t (10 ^ k))
  have hx₁ : ⌊x⌋ = t / 10 ^ k := by
    rw [hx]
    apply Int.floor_eq_iff.mpr
    constructor
    · apply sub_nonneg.mp
      field_simp
      apply div_nonneg
      · simp
        norm_cast
        exact Nat.mul_div_le t (10 ^ k)
      · positivity
    · apply sub_pos.mp
      field_simp
      norm_cast
      rw [add_mul, one_mul]
      nth_rw 1 [ht]
      gcongr
      apply Nat.mod_lt
      positivity
  have hy : ⌊y⌋ = 0 := by
      refine Int.floor_eq_iff.mpr ?_
      constructor
      · simp [hy]
      · simp
        apply lt_of_le_of_lt ?_ hk₂
        trans y * 1
        · simp
        · gcongr
          norm_cast
          exact Nat.one_le_pow' k 9
  have hx₂ : ⌊x + y⌋ = t / 10 ^ k := by
    rw [hx]
    apply Int.floor_eq_iff.mpr
    constructor
    · trans t / 10 ^ k + 0
      · simp
        apply sub_nonneg.mp
        field_simp
        apply div_nonneg
        · simp
          norm_cast
          exact Nat.mul_div_le t (10 ^ k)
        · positivity
      · simp
        assumption
    · apply lt_of_lt_of_le (b := (t + 1 : ℝ) / 10 ^ k)
      · rw [add_div]
        gcongr
        apply lt_div_iff₀ ?_ |>.mpr hk₂
        positivity
      · apply div_le_iff₀ ?_ |>.mpr
        · rw [add_mul]
          nth_rw 1 [ht]
          simp
          rw [add_assoc]
          gcongr
          · norm_cast
          · norm_cast
            apply Nat.succ_le_of_lt
            apply Nat.mod_lt
            positivity
        · positivity
  have : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ := by rw [hx₁, hx₂, hy]; simp
  unfold Int.fract
  rw [this]
  push_cast
  ring

/- We prove that if (i + k + 2) ^ n ≤ 10 ^ (Nat.digits 10 ((i + k + 2) ^ n)).length - 2, then
    ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) ≤
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) -
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (l + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ) -/
lemma tsum_le_one (n t k : ℕ) (h : ∃ i, (i + k + 2) ^ n ≤ 10 ^ (Nat.digits 10 ((i + k + 2) ^ n)).length - 2) :
    ∃ l, ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) ≤
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) -
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (l + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ) := by
  obtain ⟨r, hr⟩ := h
  use r
  -- First, show that ∑ i ∈ range l, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) ≤
  -- 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) -
  -- (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (l + k + 1), (Nat.digits 10 (j ^ n)).length : ℤ)) -
  -- if l ≥ r + 1 then (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (r + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) else 0
  have hle {l : ℕ} : ∑ i ∈ range l, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) ≤
      10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) -
      (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (l + k + 1), (Nat.digits 10 (j ^ n)).length : ℤ)) -
      if l ≥ r + 1 then (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (r + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) else 0 := by
    induction l with
    | zero =>
      simp
    | succ l ih =>
      rw [sum_range_succ]
      apply le_trans (add_le_add ih (le_refl _)) ?_
      rw [sub_sub, sub_sub, sub_add]
      apply sub_le_sub_left
      by_cases h₀ :  ¬ l ≥ r + 1
      · simp only [if_neg h₀]
        by_cases h₁ : ¬ l + 1 ≥ r + 1
        · simp only [if_neg h₁, add_zero]
          apply le_sub_left_of_add_le
          trans ((10 : ℝ) ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (l + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) * (10 ^ ((Nat.digits 10 ((l + k + 2) ^ n)).length: ℤ) - 1 + 1)
          · rw [mul_add, mul_one]
            gcongr
            · norm_cast
              rw [Int.subNatNat_eq_coe, Nat.cast_one]
              apply Int.le_sub_one_of_lt
              norm_cast
              exact Nat.lt_base_pow_length_digits'
            · simp
            · apply subset_of_eq
              ring_nf
          · rw [sub_add_cancel]
            rw [←zpow_add₀]
            · gcongr
              · simp
              · rw [sub_add]
                apply sub_le_sub_left
                rw [←add_assoc (l + k) 1 1, ←Nat.Icc_insert_succ_right (b := l + k + 1), sum_insert]
                · simp
                · simp
                · simp
            · simp
        · push_neg at h₁
          simp only [if_pos h₁, add_zero]
          have hl : l = r := by linarith only [h₀, h₁]
          rw [←hl] at hr ⊢
          apply le_sub_left_of_add_le
          trans ((10 : ℝ) ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (l + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) * (10 ^ ((Nat.digits 10 ((l + k + 2) ^ n)).length: ℤ) - 2 + (1 + 1))
          · rw [mul_add, mul_add]
            gcongr
            · apply Nat.cast_le (α := ℝ) |>.mpr at hr
              simp at hr
              apply le_of_le_of_eq hr
              rw [Nat.cast_sub]
              · push_cast
                congr
                simp
              · trans 10 ^ 1
                · simp
                · gcongr
                  simp
                  simp
            · rw [mul_one]
              apply le_of_eq
              congr 5
              ring
            · simp
          · norm_num
            rw [←zpow_add₀]
            · gcongr
              · simp
              · rw [sub_add]
                apply sub_le_sub_left
                rw [←add_assoc (l + k) 1 1, ←Nat.Icc_insert_succ_right (b := l + k + 1), sum_insert]
                · simp
                · simp
                · simp
            · simp
      · push_neg at h₀
        simp only [if_pos h₀]
        rw [if_pos (le_trans h₀ (by simp))]
        nth_rw 3 [add_sub_right_comm]
        apply add_le_add_right
        apply le_sub_left_of_add_le
        trans ((10 : ℝ) ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (l + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) * (10 ^ ((Nat.digits 10 ((l + k + 2) ^ n)).length: ℤ) - 1 + 1)
        · rw [mul_add, mul_one]
          gcongr
          · norm_cast
            rw [Int.subNatNat_eq_coe, Nat.cast_one]
            apply Int.le_sub_one_of_lt
            norm_cast
            exact Nat.lt_base_pow_length_digits'
          · simp
          · apply subset_of_eq
            ring_nf
        · rw [sub_add_cancel]
          rw [←zpow_add₀]
          · gcongr
            · simp
            · rw [sub_add]
              apply sub_le_sub_left
              rw [←add_assoc (l + k) 1 1, ←Nat.Icc_insert_succ_right (b := l + k + 1), sum_insert]
              · simp
              · simp
              · simp
          · simp
  -- Then we have ∑ i ∈ range l, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) ≤
  -- 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) -
  -- if l ≥ r + 1 then (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (r + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) else 0
  have hle (l : ℕ) : ∑ i ∈ range l, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) ≤
      10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) -
      if l ≥ r + 1 then (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (r + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) else 0 := by
    apply le_trans hle
    simp
    positivity
  -- Therefore, the result follows.
  have htendsto₁ :  Filter.Tendsto (fun l : ℕ => ∑ i ∈ range l, (10 : ℝ) ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ)) Filter.atTop (nhds (∑' i, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ))) := by
    apply HasSum.tendsto_sum_nat
    apply Summable.hasSum
    apply summable_of_sum_range_le (c := 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ))
    · intro i
      positivity
    · intro l
      apply le_trans (hle l)
      simp
      positivity
  have htendsto₂ : Filter.Tendsto (fun l : ℕ => (10 : ℝ) ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) -
      if l ≥ r + 1 then (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (r + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)) else 0) Filter.atTop (nhds (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) - (10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (r + k + 2), (Nat.digits 10 (j ^ n)).length: ℤ)))) := by
    apply Filter.Tendsto.const_add
    apply Filter.Tendsto.neg
    apply tendsto_atTop_of_eventually_const (i₀ := r + 1)
    intro l h
    simp [h]
  apply le_of_tendsto_of_tendsto htendsto₁ htendsto₂
  refine Filter.eventuallyLE_iff_all_subsets.mpr ?_
  intro _
  simp only [Filter.eventually_atTop]
  use 0
  intro _ _ _
  apply hle

/- We prove that  ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) <
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ)-/
lemma tsum_lt_one (n t k : ℕ) :  ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) <
    10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length: ℤ) := by
  -- We only need to show that there exists some i such that (i + k + 2) ^ n ≤ 10 ^ (Nat.digits 10 ((i + k + 2) ^ n)).length - 2
  have : ∃ i, (i + k + 2) ^ n ≤ 10 ^ (Nat.digits 10 ((i + k + 2) ^ n)).length - 2 := by
    by_contra h
    push_neg at h
    -- Otherwise, we have (i + k + 2) ^ n = 10 ^ (Nat.digits 10 ((i + k + 2) ^ n)).length - 1 for all i
    have {i : ℕ} : (i + k + 2) ^ n = 10 ^ (Nat.digits 10 ((i + k + 2) ^ n)).length - 1 := by
      apply le_antisymm
      · apply Nat.le_sub_one_of_lt
        apply Nat.lt_base_pow_length_digits'
      · obtain h := h i
        exact Nat.le_of_pred_lt h
    -- Thefore, 3 ∣ i + k + 2 for all i
    have {i : ℕ} : 3 ∣ (i + k + 2) ^ n := by
      rw [this]
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.sub_mod_eq_zero_of_mod_eq]
      rw [Nat.pow_mod]
      simp
    have {i : ℕ} : 3 ∣ i + k + 2 := by
      apply Nat.Prime.dvd_of_dvd_pow ?_ this
      norm_num
    obtain ⟨m, hm⟩ : 3 ∣ k := by
      suffices h : 3 ∣ 1 + k + 2
      · have : 1 + k + 2 = k + 3 := by ring
        rw [this] at h
        simp at h
        exact h
      · apply this
    rw [hm] at this
    -- which is impossible
    simp [add_comm, ←add_assoc] at this
    have {i : ℕ} : 3 ∣ i + 2 := by
      have hi : i + 2 = i + 2 + 3 * m - 3 * m := by simp
      rw [hi]
      apply Nat.dvd_sub ?_ this
      · simp
      · simp
    obtain h₀ : 3 ∣ 2 := by apply this
    norm_num at h₀
  obtain ⟨r, hr⟩ := tsum_le_one n t k this
  apply lt_of_le_of_lt hr
  simp
  positivity

/- We prove that  ⌊a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t)⌋₊ = ∑ i ∈ range k, (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ) +
    ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ)⌋₊ +
    ⌊∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ)⌋₊ -/
lemma floor_a_mul_pow' (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ))
    {k n t : ℕ} (ht : t ∈ Icc 1 (Nat.digits 10 ((k + 1) ^ n)).length) :
    ⌊a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t)⌋₊ = ∑ i ∈ range k, (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ) +
    ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ)⌋₊ +
    ⌊∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ)⌋₊ := by
  rw [floor_a_mul_pow a ha (t := t)]
  rw [floor_add]
  · ring
  · positivity
  · apply tsum_nonneg
    intro i
    positivity
  · rw [fract_add]
    · apply Int.fract_lt_one
    · apply tsum_nonneg
      intro i
      positivity
    · use ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length - ∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length - t
      constructor
      · use (k + 1) ^ n
        trans 10 ^ (↑(∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length) + ↑t - ↑(∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length) : ℤ) * 10 ^ (∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length - ∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length - t) * (↑k + 1) ^ n
        · ring
        trans 1 * (k + 1) ^ n
        · congr
          rw [←zpow_natCast, ←zpow_add₀]
          trans 10 ^ (0 : ℤ)
          · congr
            rw [Nat.cast_sub, Nat.cast_sub]
            push_cast
            ring
            · rw [←Nat.Icc_insert_succ_right, sum_insert]
              · simp
              · simp
              · simp
            · rw [←Nat.Icc_insert_succ_right, sum_insert]
              · simp at ht
                apply le_trans ht.2
                simp
              · simp
              · simp
          · simp
          · simp
        · simp
      · suffices : ∑' i : ℕ, 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (i + k + 2), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + k + 2) ^ n : ℝ) <
            1 / 10 ^ (∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length - ∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length - t)
        · apply lt_of_lt_of_eq (b := 1 / 10 ^ (∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length - ∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length - t) * 10 ^ (∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length - ∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length - t))
          · gcongr
          · field_simp
        · obtain h := tsum_lt_one n t k
          push_cast at h ⊢
          apply lt_of_lt_of_le h
          apply sub_nonneg.mp
          field_simp
          apply div_nonneg
          simp
          rw [←zpow_natCast, ←zpow_add₀]
          apply le_of_le_of_eq (b := 10 ^ (0 : ℤ))
          · gcongr
            · simp
            · rw [Nat.cast_sub, Nat.cast_sub]
              apply le_of_eq
              push_cast
              ring
              · rw [←Nat.Icc_insert_succ_right, sum_insert]
                · simp
                · simp
                · simp
              · rw [←Nat.Icc_insert_succ_right, sum_insert]
                · simp at ht
                  apply le_trans ht.2
                  simp
                · simp
                · simp
          · simp
          · positivity
          · positivity

/- We prove that ⌊a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t)⌋₊ % 10 =
    ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ)⌋₊ % 10 -/
lemma floor_a_mul_pow'' (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ))
    {k n t : ℕ} (ht : t ∈ Icc 1 (Nat.digits 10 ((k + 1) ^ n)).length) :
    ⌊a n * 10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t)⌋₊ % 10 =
    ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ)⌋₊ % 10 := by
  rw [floor_a_mul_pow' a ha (t := t) ht]
  trans (∑ i ∈ range k, (10 ^ (∑ j ∈ Ioc (i + 1) k, (Nat.digits 10 (j ^ n)).length + t) * ((i + 1) ^ n) : ℕ) +
    ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ)⌋₊ +
    0) % 10
  · congr
    simp
    obtain h := tsum_lt_one n t k
    simp at h
    apply lt_of_lt_of_le h (le_of_le_of_eq (b := (10 : ℝ) ^ (0 : ℤ)) ?_ ?_)
    · gcongr
      · simp
      · simp
        rw [←Nat.Icc_insert_succ_right]
        rw [sum_insert]
        · rw [add_comm]
          gcongr
          simp only [mem_Icc] at ht
          exact ht.2
        · simp
        · simp
    · simp
  · rw [add_zero, Nat.add_mod]
    trans (0 + ⌊10 ^ (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + t - ∑ j ∈ Icc 1 (k + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((k + 1) ^ n : ℝ)⌋₊ % 10) % 10
    · congr
      apply Nat.mod_eq_zero_of_dvd
      apply dvd_sum
      intro i hi
      simp at hi
      simp at ht
      exact ten_dvd_mul ht.1
    · simp

/- We prove that nth_bit (a n) (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + i) = nth_bit (((10 : ℝ) ^ (-(Nat.digits 10 ((k + 1) ^ n)).length : ℤ) * (k + 1) ^ n)) i -/
lemma nth_bit_a (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ))
    {k n i : ℕ} (hi : i ∈ Icc 1 (Nat.digits 10 ((k + 1) ^ n)).length) :
     nth_bit (a n) (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + i) = nth_bit (((10 : ℝ) ^ (-(Nat.digits 10 ((k + 1) ^ n)).length : ℤ) * (k + 1) ^ n)) i := by
  simp only [nth_bit]
  rw [floor_a_mul_pow'' a ha (t := i) hi]
  congr 2
  trans 10 ^ (-↑(Nat.digits 10 ((k + 1) ^ n)).length : ℤ) * 10 ^ (i : ℤ) * (k + 1 : ℝ) ^ n
  · congr 1
    rw [←zpow_add₀]
    · congr
      rw [←Nat.Icc_insert_succ_right]
      simp [sum_insert]
      ring
      simp
    · simp
  · norm_cast
    ring

/- If x , y ≥ 0 and y * 10 ^ i < 1, and Int.fract (x * 10 ^ i) + Int.fract (y * 10 ^ i) < 1. then nth_bit (x + y) i = nth_bit x i -/
lemma nth_bit_add_of_lt {x y : ℝ} (hx : x ≥ 0) (hy' : y ≥ 0) (hy : y * 10 ^ i < 1) (hx' : Int.fract (x * 10 ^ i) + Int.fract (y * 10 ^ i) < 1) : nth_bit (x + y) i = nth_bit x i := by
  simp [nth_bit, add_mul]
  rw [floor_add]
  · trans (⌊x * 10 ^ i⌋₊ + 0) % 10
    · congr
      exact Nat.floor_eq_zero.mpr hy
    · simp
  · positivity
  · positivity
  · exact hx'

/- We prove that (Nat.digits 10 x).last ≠ 0 -/
lemma digits_getLast_ne_zero (h : Nat.digits 10 x ≠ []) : (Nat.digits 10 x).getLast h ≠ 0 := by
  have hx : x = Nat.ofDigits 10 (Nat.digits 10 x) := by
    exact Eq.symm (Nat.ofDigits_digits 10 x)
  -- The last digit of Nat.digits 10 x is the first digit of x in base 10
  -- Thereofore, it is not zero.
  set l := Nat.digits 10 x with hl
  clear_value l
  simp [←hl]
  induction l generalizing x with
  | nil =>
    simp at h
  | cons a b ih =>
    by_cases hb : b = []
    · simp [hb] at hx ⊢
      rw [←hx]
      by_contra h
      simp [h] at hl
    · have : x / 10 = Nat.ofDigits 10 b := by
        simp [Nat.ofDigits_cons] at hx
        rw [hx, Nat.add_mul_div_left]
        · have : a / 10 = 0 := by
            apply Nat.div_eq_zero_iff.mpr
            right
            have ha : a = (a :: b)[0] := by simp
            rw [ha]
            simp [hl]
            apply Nat.digits_lt_base (m := x)
            · simp
            · simp
          simp [this]
        · simp
      have hl' : b = Nat.digits 10 (x / 10) := by
        trans (Nat.digits 10 x).tail
        · rw [←hl]
          simp
        · have : Nat.digits 10 x = (x % 10) :: (Nat.digits 10 (x / 10)) := by
            apply Nat.digits_eq_cons_digits_div
            · simp
            · by_contra hx
              simp [hx] at hl
          rw [this]
          simp
      obtain ih := ih (x := x / 10) (by simp [←hl', hb]) hb this hl'
      rw [List.getLast_cons]
      · simp [ih]
      · exact hb

/- We prove that nth_bit (((10 : ℝ) ^ (-(Nat.digits 10 x).length : ℤ) * x)) ((Nat.digits 10 x).length - i) = (Nat.digits 10 x)[i] -/
lemma nth_bit_x (x : ℕ) (i : Fin (Nat.digits 10 x).length) :
    nth_bit (((10 : ℝ) ^ (-(Nat.digits 10 x).length : ℤ) * x)) ((Nat.digits 10 x).length - i) = (Nat.digits 10 x)[i] := by
  have hx : x = Nat.ofDigits 10 (Nat.digits 10 x) := by exact Eq.symm (Nat.ofDigits_digits 10 x)
  set l := Nat.digits 10 x with hl
  clear_value l
  simp [←hl]
  clear i
  induction l generalizing x with
  | nil =>
    have : i.1 < 0 := by
      apply lt_of_lt_of_eq i.2
      simp [←hl]
    simp at this
  | cons a b ih =>
    simp [Nat.ofDigits_cons] at hx
    have ha : a < 10 := by
      have ha : a = (a :: b)[0] := by simp
      rw [ha]
      simp [hl]
      apply Nat.digits_lt_base (m := x)
      · simp
      · simp
    have : (10 ^ (a :: b).length)⁻¹ * (x : ℝ) = (10 ^ b.length)⁻¹ * (Nat.ofDigits 10 b : ℝ) + (10 ^ (a :: b).length)⁻¹ * a := by
      rw [hx]
      simp [pow_add, mul_add, add_comm]
      field_simp
      norm_cast
      ring
    rw [this]
    simp [List.getElem_cons]
    by_cases hi : i.val = 0
    · simp [hi, nth_bit]
      trans ⌊((10 : ℝ) * Nat.ofDigits 10 b + ↑a)⌋₊ % 10
      · congr 2
        rw [pow_add]
        have : 10 ^ b.length > 0 := by positivity
        field_simp
        ring
      · norm_cast
        rw [Nat.floor_natCast]
        rw [Nat.mul_add_mod]
        refine Nat.mod_eq_of_lt ha
    · simp [hi]
      let x' := x / 10
      let l' := Nat.digits 10 x'
      have hl' : x' = Nat.ofDigits 10 b := by
        simp [x', hx, Nat.add_mul_div_left]
        exact ha
      have hx' : b = Nat.digits 10 x' := by
        simp [x']
        suffices : a :: b = a :: Nat.digits 10 (x / 10)
        · simp at this
          exact this
        · rw [hl, Nat.digits_eq_cons_digits_div]
          · congr
            simp [hx]
            exact ha
          · simp
          · by_contra hx
            simp [hx] at hl
      let j :  Fin (Nat.digits 10 x').length := ⟨i.val - 1, by
        apply Nat.sub_lt_left_of_lt_add
        · exact Nat.one_le_iff_ne_zero.mpr hi
        · simp [←hx']
          apply lt_of_lt_of_eq i.2
          simp [←hl]
          ring⟩
      obtain ih := ih x' j hl' hx'
      simp [j] at ih
      rw [←ih]
      have : b.length - (↑i - 1) = b.length + 1 - i := by
        trans b.length - i + 1
        · refine tsub_tsub_assoc ?_ ?_
          · apply le_trans (Nat.le_pred_of_lt i.2)
            simp [←hl]
          · exact Nat.one_le_iff_ne_zero.mpr hi
        · rw [Nat.sub_add_comm]
          apply le_trans (Nat.le_pred_of_lt i.2)
          simp [←hl]
      rw [this]
      simp [hl']
      norm_cast
      apply nth_bit_add_of_lt
      · positivity
      · positivity
      · apply sub_pos.mp
        field_simp
        rw [pow_add, pow_one, mul_comm _ 10]
        apply mul_lt_mul
        · exact Nat.cast_lt_ofNat.mpr ha
        · gcongr
          · simp
          · simp
            exact Nat.one_le_iff_ne_zero.mpr hi
        · simp
        · simp
      · simp
        by_cases hb : b = []
        · simp [hb]
          apply Int.fract_lt_one
        · rw [fract_add]
          · apply Int.fract_lt_one
          · positivity
          · use i - 1
            constructor
            · use Nat.ofDigits 10 b
              field_simp
              rw [mul_assoc]
              congr
              rw [←pow_add]
              congr
              rw [←Nat.add_sub_assoc, Nat.sub_add_cancel]
              · simp
              · apply le_trans (le_of_lt i.2)
                simp [←hl]
              · exact Nat.one_le_iff_ne_zero.mpr hi
            · apply sub_pos.mp
              field_simp
              rw [pow_add, pow_one, mul_comm _ 10, mul_assoc]
              apply mul_lt_mul
              · simp [ha]
              · rw [←pow_add]
                gcongr
                · simp
                · rw [←Nat.add_sub_assoc, Nat.sub_add_cancel]
                  · simp
                  · apply le_trans (le_of_lt i.2)
                    simp [←hl]
                  · exact Nat.one_le_iff_ne_zero.mpr hi
              · positivity
              · simp

/- We prove that nth_bit (((10 : ℝ) ^ (-(Nat.digits 10 x).length : ℤ) * x)) i =
    (Nat.digits 10 x)[(Nat.digits 10 x).length - i] = -/
lemma nth_bit_x' (x : ℕ) (hi : i ∈ Icc 1 (Nat.digits 10 x).length) :
    nth_bit (((10 : ℝ) ^ (-(Nat.digits 10 x).length : ℤ) * x)) i =
    (Nat.digits 10 x)[(Nat.digits 10 x).length - i]'(by simp only [mem_Icc] at hi; exact Nat.div_rec_lemma hi) := by
  let i : Fin (Nat.digits 10 x).length := ⟨(Nat.digits 10 x).length - i, by simp only [mem_Icc] at hi; exact Nat.div_rec_lemma hi⟩
  obtain h := nth_bit_x x i
  simp [i] at h
  rw [←h]
  simp
  congr 1
  symm
  refine Nat.sub_sub_self ?_
  simp at hi
  exact hi.2

/- nth_bit (a n) (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + i) = (Nat.digits 10 ((k + 1) ^ n))[(Nat.digits 10 ((k + 1) ^ n)).length - i] -/
lemma nth_bit_a_eq (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ))
    {k n i : ℕ} (hi : i ∈ Icc 1 (Nat.digits 10 ((k + 1) ^ n)).length) :
    nth_bit (a n) (∑ j ∈ Icc 1 k, (Nat.digits 10 (j ^ n)).length + i) = (Nat.digits 10 ((k + 1) ^ n))[(Nat.digits 10 ((k + 1) ^ n)).length - i]'(by simp only [mem_Icc] at hi; exact Nat.div_rec_lemma hi) := by
  rw [nth_bit_a a ha hi]
  simp at hi
  obtain ⟨h₁, h₂⟩ := hi
  obtain h := nth_bit_x' ((k + 1) ^ n) hi
  push_cast at h
  exact h

/- Nat.digits 10 (10 ^ n) = List.replicate n 0 ++ Nat.digits 10 1 -/
lemma digits_ten_pow : Nat.digits 10 (10 ^ n) = List.replicate n 0 ++ Nat.digits 10 1 := by
  rw [←Nat.digits_base_pow_mul]
  all_goals simp

/- If  i < (Nat.digits 10 (10 ^ n)).length - 1,  (Nat.digits 10 (10 ^ n))[i] = 0 -/
lemma digits_pow {n : ℕ} (hi : i < (Nat.digits 10 (10 ^ n)).length - 1 ) : (Nat.digits 10 (10 ^ n))[i]'(by apply lt_trans hi; simp) = 0 := by
  simp only [digits_ten_pow]
  rw [List.getElem_append]
  simp
  have : (Nat.digits 10 (10 ^ n)).length = n + 1 := by
    have : 10 ^ n = 10 ^ n * 1 := by ring
    rw [this, Nat.digits_base_pow_mul]
    simp
    simp
    simp
  rw [this] at hi
  simp at hi
  exact hi

/- (Nat.digits 10 ((10 ^ (M + n) + 1) ^ 1))[(Nat.digits 10 ((10 ^ (M + n) + 1) ^ 1)).length - 1] ≠ 0 -/
lemma digits_add_last (hn : n > 0) : (Nat.digits 10 ((10 ^ (M + n) + 1) ^ 1))[(Nat.digits 10 ((10 ^ (M + n) + 1) ^ 1)).length - 1] ≠ 0 := by
  -- This is exactly the last digit of 10 ^ (M + n) + 1
  simp
  have h₀ : M + n = M + n - 1 + 1 := by
    rw [Nat.sub_add_cancel]
    apply Nat.le_of_pred_lt
    simp
    simp [hn]
  have heq : (10 ^ (M + n) + 1) / 10 = 10 ^ (M + n - 1) := by
    nth_rw 1 [h₀]
    rw [Nat.pow_add_one']
    rw [Nat.mul_add_div]
    · simp
    · simp
  have hlen : (Nat.digits 10 ((10 ^ (M + n) + 1) / 10)).length = M + n := by
    rw [heq]
    simp only [digits_ten_pow]
    simp
    exact id (Eq.symm h₀)
  simp only [hlen]
  simp only [List.getElem_cons, heq]
  have : M + n ≠ 0 := by apply ne_of_gt; exact Nat.add_pos_right M hn
  simp only [dif_neg this, digits_ten_pow]
  simp

/- Show that m ≤ 10 ^ m -/
lemma le_pow_n : m ≤ 10 ^ m := by
  -- prove by induction on m
  induction m with
  | zero => simp
  | succ m ih =>
    simp [Nat.pow_add_one]
    by_cases hm : m = 0
    · simp [hm]
    · simp at hm
      trans m + m
      · simp
        exact Nat.one_le_iff_ne_zero.mpr hm
      trans m * 2
      · apply le_of_eq
        ring
      · gcongr
        simp

/-2. (SWE 2) Let $f(x)=x^{n}$ where $n$ is a fixed positive integer and $x=$ $1,2, \ldots$.
Is the decimal expansion $a=0 . f(1) f(2) f(3) \ldots$ rational for any value of $n$ ?
 The decimal expansion of $a$ is defined as follows: If $f(x)=d_{1}(x) d_{2}(x) \ldots$ $\ldots d_{r(x)}(x)$
 is the decimal expansion of $f(x)$, then $a=0.1 d_{1}(2) d_{2}(2) \ldots$ $\ldots d_{r(2)}(2) d_{1}(3) \ldots d_{r(3)}(3) d_{1}(4) \ldots$.-/
theorem number_theory_24031 (a : ℕ → ℝ) (ha : a = fun n : ℕ => ∑' i : ℕ, 10 ^ (-∑ j ∈ Icc 1 (i + 1), (Nat.digits 10 (j ^ n)).length : ℤ) * ((i + 1) ^ n : ℝ)) :
    ¬ ∀ n, n > 0 → ∃ r : ℚ, r = a n := by
  simp
  use 1, (by norm_num)
  by_contra h
  simp at h
  -- 2. No. If $a$ were rational, its decimal expansion would be periodic from some point.
  obtain ⟨x, hx⟩ := h
  have hx_pos : x > 0 := by
    apply Rat.cast_lt (K := ℝ) |>.mp
    rw [hx, ha]
    push_cast
    apply tsum_pos ?_ ?_ 0
    · simp
    · obtain h := summable_a 1
      push_cast at h
      exact h
    · intro i
      positivity
  obtain ⟨n, hn, M, hM⟩ := eventually_zero_of_periodic hx_pos
  -- Let $p$ be the number of decimals in the period.
  -- Since $f\left(10^{2 p}\right)$ has $2 n p$ zeros,
  let m := ∑ j ∈ Icc 1 (10 ^ (M + n + 2) - 1), (Nat.digits 10 j).length + 2
  have hm : m ≥ M := by
    trans ∑ j ∈ Icc 1 (10 ^ (M + n + 2) - 1), 1 + 2
    · simp only [m]
      apply add_le_add_right
      apply sum_le_sum
      intro i hi
      by_contra h
      simp at h
      apply Nat.digits_eq_nil_iff_eq_zero.mp at h
      simp [h] at hi
    · simp
      trans 10 ^ M
      · exact le_pow_n
      · trans 10 ^ ( M + n + 2)
        · gcongr
          simp
          simp [add_assoc]
        · nth_rw 3 [show 2 = 1 + 1 by simp]
          nth_rw 2 [←add_assoc _ 1 1]
          rw [Nat.sub_add_cancel]
          · simp
          · exact Nat.one_le_pow' (M + n + 2) 9
  -- it contains a full periodic part
  have hzero : ∀ k ∈ Ico m (m + n), nth_bit (↑x) k = 0 := by
    intro k hk
    simp at hk
    let t := k - ∑ j ∈ Icc 1 (10 ^ (M + n + 2) - 1), (Nat.digits 10 (j ^ 1)).length
    have ht : k = ∑ j ∈ Icc 1 (10 ^ (M + n + 2) - 1), (Nat.digits 10 (j ^ 1)).length + t := by
      simp [t]
      rw [Nat.add_sub_cancel']
      simp [m] at hk
      apply le_trans ?_ hk.1
      simp
    rw [ht, hx, nth_bit_a_eq a ha (n := 1)]
    · have : (10 ^ (M + n + 2) - 1 + 1) ^ 1 = 10 ^ (M + n + 2) := by
        simp
        rw [Nat.sub_add_cancel]
        exact Nat.one_le_pow' (M + n + 2) 9
      simp only [this]
      rw [digits_pow]
      refine Nat.sub_lt_sub_left ?_ ?_
      · have : (Nat.digits 10 (10 ^ (M + n + 2))).length = M + n + 2 + 1 := by
          have : 10 ^ (M + n + 2) = 10 ^ (M + n + 2) * 1 := by ring
          rw [this, Nat.digits_base_pow_mul]
          simp
          simp
          simp
        rw [this]
        simp
      · simp [t]
        apply Nat.lt_sub_of_add_lt
        apply lt_of_lt_of_le ?_ hk.1
        simp [m, add_comm]
    · simp [t]
      constructor
      · apply Nat.le_sub_of_add_le
        apply le_trans ?_ hk.1
        simp [m, add_comm]
      · trans m + n
        · apply le_of_lt hk.2
        · simp [m]
          trans ∑ x ∈ Icc 1 (10 ^ (M + n + 2) - 1), (Nat.digits 10 x).length + ((Nat.digits 10 ((10 ^ (M + n + 2) - 1 + 1) / 10)).length + 1)
          · rw [add_assoc]
            apply add_le_add
            · simp
            · have : (Nat.digits 10 ((10 ^ (M + n + 2) - 1 + 1) / 10)).length = n + 2 + M := by
                have : (10 ^ (M + n + 2) - 1 + 1) / 10 = 10 ^ (M + n + 1) * 1 := by
                  rw [Nat.sub_add_cancel]
                  · have : M + n + 2 = M + n + 1 + 1 := by ring
                    rw [this, Nat.pow_add_one]
                    field_simp
                  · exact Nat.one_le_pow' (M + n + 2) 9
                rw [this, Nat.digits_base_pow_mul]
                · simp
                  ring
                all_goals simp
              rw [this, add_assoc, add_comm]
              simp
          · apply le_of_eq
            ring
  -- hence the period would consist only of zeros, which is impossible.
  apply hM m hm at hzero
  -- We find the k-th digit of a is non-zero, where k := ∑ j ∈ Icc 1 (10 ^ (M + n + 2)), (Nat.digits 10 (j ^ 1)).length + 1
  let k := ∑ j ∈ Icc 1 (10 ^ (M + n + 2)), (Nat.digits 10 (j ^ 1)).length + 1
  have hk : k ≥ m := by
    simp [k, m]
    have : 10 ^ (M + n + 2) = 10 ^ (M + n + 2) - 1 + 1 := by
      rw [Nat.sub_add_cancel]
      exact Nat.one_le_pow' (M + n + 2) 9
    rw [this, ←Nat.Icc_insert_succ_right]
    simp
    rw [add_comm]
    gcongr
    · simp
    · simp
  have hne_zero : nth_bit (↑x) k ≠ 0 := by
    rw [hx, nth_bit_a_eq a ha (n := 1)]
    · exact digits_add_last (by simp)
    · simp
  apply hzero k at hk
  simp [hk] at hne_zero
