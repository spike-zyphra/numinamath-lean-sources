import Mathlib
open Nat

/-
  2017 prime numbers  $p_1,...,p_{2017}$  are given.
  Prove that  $\prod_{i < j} (p_i^{p_j}-p_j^{p_i})$  is divisible by 5777.
-/
theorem number_theory_8963 (p : Fin 2017 → ℕ) (h₀ : ∀ i : Fin 2017, (p i).Prime) :
    (5777 : ℤ) ∣ (∏ j ∈ Finset.range 2017, ∏ i ∈ Finset.range j, ((p i) ^ (p j) - (p j) ^ (p i))) := by

  -- if 2017 primes are not distinct, then prod = 0, trivial
  have non_inj (h : ¬ Function.Injective p) :
      ∏ j ∈ Finset.range 2017, ∏ i ∈ Finset.range j, ((p i) ^ (p j) - (p j : ℤ) ^ (p i)) = 0 := by
    simp [Function.Injective] at h
    obtain ⟨x₁, ⟨x₂, ⟨heq, hneq⟩⟩⟩ := h
    wlog hle : x₁ < x₂ with H
    · push_neg at hle
      rcases lt_or_eq_of_le hle with h | h
      · exact H p h₀ x₂ x₁ (Eq.symm heq) (Ne.symm hneq) h
      · rw [eq_comm] at h
        contradiction
    · have hx₂ : x₂.val ∈ Finset.range 2017 := by simp
      apply Finset.prod_eq_zero hx₂
      have hx₁ : x₁.val ∈ Finset.range x₂ := by simp [hle]
      apply Finset.prod_eq_zero hx₁
      simp [heq]

  -- if {2, 3, 13, 53, 109} are not in the list, we can find i < j and 53 ∣ (p i) ^ (p j) - (p j) ^ (p i)
  have hcoprime (hinj : Function.Injective p) (s : Finset (Fin 2017)) (hs : s.card > 53)
      (hco : ∀ i : Fin 2017, i ∈ s → p i ∉ ({2, 3, 13, 53, 109} : Finset ℕ)) : ∃ i j, i < j ∧ (53 : ℤ) ∣ (p i) ^ (p j) - (p j) ^ (p i) := by

    -- apply pigeonhold principle to find i j such that p i ^ b i = p j ^ b j [mod 53]
    let b (i : Fin 2017) := (((p i) : ZMod 52).inv).val
    let f (i : Fin 2017) := ((p i) : ZMod 53) ^ (b i)
    let t := (@Set.univ (ZMod 53)).toFinset
    have hf : ∀ a ∈ s, f a ∈ t := by simp [t]
    have hn : t.card * 1 < s.card := by
      simp [t, hs]
    obtain ⟨y, ⟨_, hlt⟩⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
    obtain ⟨i, ⟨j, ⟨hi, ⟨hj, hneq⟩⟩⟩⟩ := Finset.one_lt_card_iff.mp hlt
    simp at hi hj
    obtain ⟨hi, hfi⟩ := hi
    obtain ⟨hj, hfj⟩ := hj
    simp [f] at hfi hfj
    have : Fact (Nat.Prime 53) := by
      refine { out := ?out }
      norm_num

    -- prove ∃ k, b i * p i = k * 52 + 1
    have hinv (i : Fin 2017) (hi : i ∈ s) : ∃ k, b i * p i = k * 52 + 1 := by
      have : b i * p i = (1 : ZMod 52) := by
        simp only [b]
        apply ZMod.val_inv_mul
        rw [show 52 = 2 * 2 * 13 by simp]
        obtain h := hco i hi
        apply Coprime.mul_right
        · apply Coprime.mul_right
          all_goals
          apply (coprime_primes (h₀ i) ?_).mpr
          · by_contra heq
            simp [heq] at h
          · norm_num
        · apply (coprime_primes (h₀ i) ?_).mpr
          · by_contra heq
            simp [heq] at h
          · norm_num
      have : b i * p i ≡ 1 [MOD 52] := by
        apply (ZMod.eq_iff_modEq_nat 52).mp
        simp [this]
      have : b i * p i % 52 = 1 := by exact this
      let k := (b i * p i / 52)
      use k
      simp [k]
      rw [<-this]
      exact Eq.symm (div_add_mod' (b i * p i) 52)

    -- prove p i ^ (b i * p i) = p i by FLT
    have hpow (i : Fin 2017) (hi : i ∈ s) : p i ^ (b i * p i) =  (p i : ZMod 53) := by
      have hfermat : p i ^ 52 = (1 : ZMod 53) := by
        apply ZMod.pow_card_sub_one_eq_one
        have : Fact (Nat.Prime (p i)) := by
          refine { out := ?_}
          exact h₀ i
        apply ZMod.prime_ne_zero
        obtain h := hco i hi
        by_contra heq
        simp [<-heq] at h
      obtain ⟨k, hk⟩ := hinv i hi
      simp [hk, pow_add]
      suffices h : ↑(p i) ^ (k * 52) = (1 : ZMod 53)
      · simp [h]
      · rw [mul_comm, pow_mul]
        suffices h : p i ^ 52 = (1 : ZMod 53)
        · simp [h]
        · exact hfermat

    -- p i ^ b i = p j ^ b j → pi ^ (bi * pi * pj) = pj ^ (pj * pi * pj)
    rw [<-hfi] at hfj
    have : (i : Fin 2017) = i := by
      apply Fin.ext
      simp [hi]
    rw [this] at hfj
    have : (j : Fin 2017) = j := by
      apply Fin.ext
      simp [hj]
    rw [this] at hfj
    have heq : (p i : ZMod 53) ^ (b i * p i * p j) = p j ^ (b j * p j * p i) := by
      calc
        (p i : ZMod 53) ^ (b i * p i * p j) = ((p i ^ b i) ^ p i) ^ p j := by rw [pow_mul, pow_mul]
        _ = ((p j ^ b j) ^ p i) ^ p j:= by rw [<-hfj]
        _ = p j ^ (b j * p i * p j) := by rw [pow_mul, pow_mul]
        _ = p j ^ (b j * p j * p i) := by ring

    -- pi ^ (bi * pi * pj) = pi ^ pj
    have : (p i : ZMod 53) ^ (b i * p i * p j) = (p i : ZMod 53) ^ p j := by
      rw [pow_mul]
      rw [hpow i hi]
    rw [this] at heq

    -- pj ^ (bj * pj * pi) = pj ^ pi
    have : p j ^ (b j * p j * p i) = (p j : ZMod 53) ^ p i := by
      rw [pow_mul]
      rw [hpow j hj]
    rw [this] at heq

    rcases lt_or_gt_of_ne hneq with h | h
    · use i, j
      constructor
      · simp [h]
      · rw [show (53 : ℤ) = (53 : ℕ) by norm_num]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (↑(p i) ^ p j - ↑(p j) ^ p i) 53).mp
        simp
        exact sub_eq_zero_of_eq heq
    · use j, i
      constructor
      · simp [h]
      · rw [show (53 : ℤ) = (53 : ℕ) by norm_num]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 53).mp
        simp
        rw [eq_comm] at heq
        exact sub_eq_zero_of_eq heq

  -- if {2, 3, 13, 53, 109} are not in the list, we can find i < j and 109 ∣ (p i) ^ (p j) - (p j) ^ (p i)
  have hcoprime' (hinj : Function.Injective p) (s : Finset (Fin 2017)) (hs : s.card > 109)
      (hco : ∀ i : Fin 2017, i ∈ s → p i ∉ ({2, 3, 13, 53, 109} : Finset ℕ)) : ∃ i j, i < j ∧ (109 : ℤ) ∣ (p i) ^ (p j) - (p j) ^ (p i) := by
    -- apply pigeonhold principle to find i j such that p i ^ b i = p j ^ b j [mod 109]
    let b (i : Fin 2017) := (((p i) : ZMod 108).inv).val
    let f (i : Fin 2017) := ((p i) : ZMod 109) ^ (b i)
    let t := (@Set.univ (ZMod 109)).toFinset
    have hf : ∀ a ∈ s, f a ∈ t := by simp [t]
    have hn : t.card * 1 < s.card := by
      simp [t, hs]
    obtain ⟨y, ⟨_, hlt⟩⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
    obtain ⟨i, ⟨j, ⟨hi, ⟨hj, hneq⟩⟩⟩⟩ := Finset.one_lt_card_iff.mp hlt
    simp at hi hj
    obtain ⟨hi, hfi⟩ := hi
    obtain ⟨hj, hfj⟩ := hj
    simp [f] at hfi hfj
    have : Fact (Nat.Prime 109) := by
      refine { out := ?_ }
      norm_num

    -- prove ∃ k, b i * p i = k * 108 + 1
    have hinv (i : Fin 2017) (his : i ∈ s) : ∃ k, b i * p i = k * 108 + 1 := by
      have : b i * p i = (1 : ZMod 108) := by
        simp only [b]
        apply ZMod.val_inv_mul
        rw [show 108 = (2 ^ 2) * 3 ^ 3 by simp]
        obtain h := hco i his
        apply Coprime.mul_right
        all_goals
        apply Coprime.pow_right
        apply (coprime_primes (h₀ i) ?_).mpr
        · by_contra heq
          simp [heq] at h
        · norm_num
      have : b i * p i ≡ 1 [MOD 108] := by
        apply (ZMod.eq_iff_modEq_nat 108).mp
        simp [this]
      have : b i * p i % 108 = 1 := by exact this
      let k := (b i * p i / 108)
      use k
      simp [k]
      rw [<-this]
      exact Eq.symm (div_add_mod' (b i * p i) 108)

    -- prove p i ^ (b i * p i) = p i by FLT
    have hpow (i : Fin 2017) (his : i ∈ s) : p i ^ (b i * p i) =  (p i : ZMod 109) := by
      have hfermat : p i ^ 108 = (1 : ZMod 109) := by
        apply ZMod.pow_card_sub_one_eq_one
        have : Fact (Nat.Prime (p i)) := by
          refine { out := ?_}
          exact h₀ i
        apply ZMod.prime_ne_zero
        obtain h := hco i his
        by_contra heq
        simp [<-heq] at h
      obtain ⟨k, hk⟩ := hinv i his
      simp [hk, pow_add]
      suffices h : ↑(p i) ^ (k * 108) = (1 : ZMod 109)
      · simp [h]
      · rw [mul_comm, pow_mul]
        suffices h : p i ^ 108 = (1 : ZMod 109)
        · simp [h]
        · exact hfermat

    -- p i ^ b i = p j ^ b j → pi ^ (bi * pi * pj) = pj ^ (pj * pi * pj)
    rw [<-hfi] at hfj
    have heq : (p i : ZMod 109) ^ (b i * p i * p j) = p j ^ (b j * p j * p i) := by
      calc
        (p i : ZMod 109) ^ (b i * p i * p j) = ((p i ^ b i) ^ p i) ^ p j := by rw [pow_mul, pow_mul]
        _ = ((p j ^ b j) ^ p i) ^ p j:= by rw [<-hfj]
        _ = p j ^ (b j * p i * p j) := by rw [pow_mul, pow_mul]
        _ = p j ^ (b j * p j * p i) := by ring

    -- pi ^ (bi * pi * pj) = pi ^ pj
    have : (p i : ZMod 109) ^ (b i * p i * p j) = (p i : ZMod 109) ^ p j := by
      rw [pow_mul]
      rw [hpow i hi]
    rw [this] at heq

    -- pj ^ (bj * pj * pi) = pj ^ pi
    have : p j ^ (b j * p j * p i) = (p j : ZMod 109) ^ p i := by
      rw [pow_mul]
      rw [hpow j hj]
    rw [this] at heq

    rcases lt_or_gt_of_ne hneq with h | h
    · use i, j
      constructor
      · simp [h]
      · rw [show (109 : ℤ) = (109 : ℕ) by norm_num]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd (↑(p i) ^ p j - ↑(p j) ^ p i) 109).mp
        simp
        exact sub_eq_zero_of_eq heq
    · use j, i
      constructor
      · simp [h]
      · rw [show (109 : ℤ) = (109 : ℕ) by norm_num]
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 109).mp
        simp
        rw [eq_comm] at heq
        exact sub_eq_zero_of_eq heq

  wlog hdistinct : Function.Injective p
  · -- trivial
    rw [non_inj hdistinct]
    simp
  · let t := ({2, 3, 13, 53, 109} : Finset ℕ)
    have hf : Set.InjOn p (p ⁻¹' t) := by
      intro a₁ _ a₂ _ heq
      exact hdistinct heq
    -- remove preimage of 2, 3, 13, 53, 109
    let s1 := Finset.preimage ({2, 3, 13, 53, 109} : Finset ℕ) p hf
    have hsub : Finset.image p s1 ⊆ ({2, 3, 13, 53, 109} : Finset ℕ) := by
      intro x hx
      simp [s1] at hx
      obtain ⟨a, ⟨ha, hx⟩⟩ := hx
      simp [<-hx, ha]
    have : s1.card = (Finset.image p s1).card := by
      apply Eq.symm
      apply Finset.card_image_of_injective
      exact hdistinct
    have hs1 : s1.card ≤ 5 := by
      simp [this]
      apply Finset.card_le_card hsub
    let s2 := @Finset.Icc (Fin 2017) _ _ (0 : Fin 2017) (2016 : Fin 2017)
    have hs2 : s2.card ≥ 2017 := by
      simp [s2]
      norm_cast
    let s : Finset (Fin 2017) :=
      (@Finset.Icc (Fin 2017) _ _ (0 : Fin 2017) (2016 : Fin 2017)) \ s1
    have hs : s.card ≥ 2012 := by
      calc
        s.card ≥ (@Finset.Icc (Fin 2017) _ _ (0 : Fin 2017) (2016 : Fin 2017)).card - (Finset.preimage ({2, 3, 13, 53, 109} : Finset ℕ) p hf).card := by
          simp only [s, s1]
          apply Finset.le_card_sdiff
        _ ≥ 2017 - 5 := by rel [hs1, hs2]
        _ = 2012 := by simp
    -- there are still > 53 / 109 numbers
    have hs1 : s.card > 53 := by
      calc
        s.card ≥ 2012 := by exact hs
        _ > 53 := by exact Nat.lt_of_sub_eq_succ rfl
    have hs2 : s.card > 109 := by
      calc
        s.card ≥ 2012 := by exact hs
        _ > 109 := by exact Nat.lt_of_sub_eq_succ rfl
    have hnotin : ∀ i ∈ s, p i ∉ ({2, 3, 13, 53, 109} : Finset ℕ) := by
      intro i hi
      simp [s] at hi
      obtain h := hi.right
      simp [s1] at h
      simp [h]
    -- if {2, 3, 13, 53, 109} are not in the list, then apply the two lemmas
    rw [show (5777 : ℤ) = 53 * 109 by norm_num]
    apply Int.ofNat_dvd_left.mpr
    apply Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
    · apply Int.ofNat_dvd_left.mp
      apply (Prime.dvd_finset_prod_iff ?_ _).mpr
      · have ⟨i, ⟨j, ⟨hlt, hdvd⟩⟩⟩ := hcoprime hdistinct s hs1 hnotin
        have : j.val ∈ Finset.range 2017 := by simp
        use j, this
        apply (Prime.dvd_finset_prod_iff ?_ _).mpr
        · have : i.val ∈ Finset.range j := by simp [hlt]
          use i, this
          simp [hdvd]
        · refine prime_iff_prime_int.mp ?_
          norm_num
      · refine prime_iff_prime_int.mp ?_
        norm_num
    · apply Int.ofNat_dvd_left.mp
      apply (Prime.dvd_finset_prod_iff ?_ _).mpr
      · have ⟨i, ⟨j, ⟨hlt, hdvd⟩⟩⟩ := hcoprime' hdistinct s hs2 hnotin
        have : j.val ∈ Finset.range 2017 := by simp
        use j, this
        apply (Prime.dvd_finset_prod_iff ?_ _).mpr
        · have : i.val ∈ Finset.range j := by simp [hlt]
          use i, this
          simp [hdvd]
        · refine prime_iff_prime_int.mp ?_
          norm_num
      · refine prime_iff_prime_int.mp ?_
        norm_num
