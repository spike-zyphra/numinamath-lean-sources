import Mathlib

/- Find the number of positive integers $n$ less than $2017$ such that
$$
1+n+\frac{n^2}{2!}+\frac{n^3}{3!}+\frac{n^4}{4!}+\frac{n^5}{5!}+\frac{n^6}{6!}
$$
 is an integer. -/
theorem algebra_97330 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 2017 ∧ ∃ k : ℕ, (1 + n + (n ^ 2) / 2 + (n ^ 3) / 6 + (n ^ 4) / 24 + (n ^ 5) / 120 + (n ^ 6) / 720 : ℚ) = k} = 134 := by
  /- A short proof which checks all numbers between 0 and 2017 with native_decide:
     field_simp; norm_num; norm_cast
     set s := {n : ℕ | _}
     suffices h : s = Finset.filter (fun n : ℕ => 24883200 ∣ (((((1 + n) * 2 + n ^ 2) * 6 + n ^ 3 * 2) * 24 + n ^ 4 * 12) * 120 + n ^ 5 * 288) * 720 + n ^ 6 * 34560) (Finset.Ioo 0 2017) by
       rw [h]
       rw [Set.ncard_coe_Finset]
       native_decide
     ext n
     simp [s, Nat.instDvd, mul_comm]
     aesop -/
  set s := {n : ℕ | _}
  -- it is enought to show that the set from the theorem statement is equal to the set of
  -- all natural numbers n ∈ (0, 2016] such that n ≡ 0 [MOD 30] or n ≡ 24 [MOD 30]
  suffices h : s = Finset.filter (fun n : ℕ => n ≡ 0 [MOD 30] ∨ n ≡ 24 [MOD 30]) (Finset.Ioc 0 2016) by
    rw [h, Set.ncard_coe_Finset, Finset.filter_or, Finset.card_union_of_disjoint]
    · zify
      -- use Nat.Ioc_filter_modEq_card theorem to compute sizes of sets
      -- {n | n ∈ (0, 2016] ∧ n ≡ 0 [MOD 30]}
      -- {n | n ∈ (0, 2016] ∧ n ≡ 24 [MOD 30]}
      rw [Nat.Ioc_filter_modEq_card 0 _ (by norm_num)]
      rw [Nat.Ioc_filter_modEq_card 0 _ (by norm_num)]
      norm_num
    -- show that {n | n ∈ (0, 2016] ∧ n ≡ 0 [MOD 30]} and {n | n ∈ (0, 2016] ∧ n ≡ 24 [MOD 30]}
    -- are disjoint
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext n
    simp [Nat.modEq_iff_dvd]
    omega
  ext n
  simp [s]
  -- simplify the expression and get the following condition
  -- ∃ k, 720 + 720 * n + 360 * n ^ 2 + 120 * n ^ 3 + 30 * n ^ 4 + 6 * n ^ 5 + n ^ 6 = k * 720
  have heq : (1 + n + n ^ 2 / 2 + n ^ 3 / 6 + n ^ 4 / 24 + n ^ 5 / 120 + n ^ 6 / 720 : ℚ)
      = (720 + 720 * n + 360 * n ^ 2 + 120 * n ^ 3 + 30 * n ^ 4 + 6 * n ^ 5 + n ^ 6) / 720 := by
    field_simp
    ring
  rw [heq]; clear heq
  field_simp
  norm_cast
  simp_rw [show n < 2017 ↔ n ≤ 2016 by omega, and_assoc, and_congr_right_iff]
  intro hn1 hn2
  constructor
  · intro ⟨k, hk⟩
    -- suppose that 720 + 720 * n + 360 * n ^ 2 + 120 * n ^ 3 + 30 * n ^ 4 + 6 * n ^ 5 + n ^ 6 = k * 720
    -- for some k and show n ≡ 0 [MOD 30] or n ≡ 24 [MOD 30]
    -- rewrite the above expression modulo 2, 3, and 5
    have h2 := congr_arg (fun n : ℕ => (n : ZMod 2)) hk
    have h3 := congr_arg (fun n : ℕ => (n : ZMod 3)) hk
    have h5 := congr_arg (fun n : ℕ => (n : ZMod 5)) hk
    push_cast at h2 h3 h5
    -- we get the following equalities
    -- n ^ 6 = 0 (mod 2)
    -- n ^ 6 = 0 (mod 3)
    -- n ^ 6 + n ^ 5 = 0 (mod 5)
    reduce_mod_char at h2 h3 h5
    -- 2, 3, and 5 are prime numbers so ZMod 2, ZMod 3, and ZMod 5 are fields
    have ⟨hp2, hp3, hp5⟩ : Fact (2).Prime ∧ Fact (3).Prime ∧ Fact (5).Prime := ⟨⟨Nat.prime_two⟩, ⟨Nat.prime_three⟩, ⟨Nat.prime_five⟩⟩
    have hz (m : ℕ) : (0 : ZMod m) = (0 : ℕ) := by norm_cast
    -- from n ^ 6 = 0 (mod 2) we get n ≡ 0 [MOD 2]
    rw [pow_eq_zero_iff (by norm_num), hz, ZMod.natCast_eq_natCast_iff] at h2
    -- from n ^ 6 = 0 (mod 3) we get n ≡ 0 [MOD 3]
    rw [pow_eq_zero_iff (by norm_num), hz, ZMod.natCast_eq_natCast_iff] at h3
    -- combine n ≡ 0 [MOD 2] and n ≡ 0 [MOD 3] with CRT and get n ≡ 0 [MOD 6]
    have h6 : n ≡ 0 [MOD 6] := by
      have x := Nat.chineseRemainder_modEq_unique (by norm_num) h2 h3
      simp [Nat.chineseRemainder, Nat.chineseRemainder'] at x
      exact x
    rw [show (n : ZMod 5) ^ 5 + n ^ 6 = n ^ 5 * (n + 1) by ring] at h5
    -- solve the equation n ^ 6 + n ^ 5 = 0 (mod 5) and get
    -- n ≡ 0 [MOD 5] or n ≡ 4 [MOD 5]
    rw [mul_eq_zero, pow_eq_zero_iff (by norm_num), add_eq_zero_iff_eq_neg] at h5
    reduce_mod_char at h5
    simp_rw [hz, show (4 : ZMod 5) = (4 : ℕ) by norm_cast, ZMod.natCast_eq_natCast_iff] at h5
    cases' h5 with h5 h5
    · left
      -- if n ≡ 0 [MOD 5] then CRT and n ≡ 0 [MOD 6] imply n ≡ 0 [MOD 30]
      have x := Nat.chineseRemainder_modEq_unique (by norm_num) h5 h6
      simp [Nat.chineseRemainder, Nat.chineseRemainder'] at x
      exact x
    · right
      -- if n ≡ 4 [MOD 5] then CRT and n ≡ 0 [MOD 6] imply n ≡ 24 [MOD 30]
      have x := Nat.chineseRemainder_modEq_unique (by norm_num) h5 h6
      simp [Nat.chineseRemainder, Nat.chineseRemainder', Nat.xgcd, Nat.xgcdAux] at x
      exact x
  · intro h
    -- suppose now that n ≡ 0 [MOD 30] or n ≡ 24 [MOD 30]
    -- and show that ∃ k, 720 + 720 * n + 360 * n ^ 2 + 120 * n ^ 3 + 30 * n ^ 4 + 6 * n ^ 5 + n ^ 6 = k * 720
    cases' h with h h
    · rw [Nat.modEq_zero_iff_dvd] at h
      have ⟨k, hk⟩ := h
      -- if n ≡ 0 [MOD 30] then n = 30 * k for some k
      -- and we can use the following value to finish the proof
      use 1012500 * k ^ 6 + 202500 * k ^ 5 + 33750 * k ^ 4 + 4500 * k ^ 3 + 450 * k ^ 2 + 30 * k + 1
      rw [hk]
      ring
    · cases' lt_or_ge n 24 with hn hn
      · dsimp [Nat.ModEq] at h
        omega
      symm at h
      rw [Nat.modEq_iff_dvd' hn] at h
      have ⟨k, hk⟩ := h
      -- if n ≡ 24 [MOD 30] then n = 30 * k + 24 for some k
      -- and we can use the following value to finish the proof
      use 1012500*k ^ 6 + 5062500*k ^ 5 + 10563750*k ^ 4 + 11776500*k ^ 3 + 7398450*k ^ 2 + 2483886*k + 348217
      rw [show n = 30 * k + 24 by omega]
      ring