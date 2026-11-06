import Mathlib

/- 6. (USS) ${ }^{\mathrm{IMO} 04}$ Let $A$ be the sum of the digits of the number $16^{16}$ and $B$ the sum of the digits of the number $A$. Find the sum of the digits of the number $B$ without calculating $16^{16}$. -/
theorem other_25068 : (Nat.digits 10 (Nat.digits 10 (Nat.digits 10 (16 ^ 16)).sum).sum).sum = 7 := by
  -- The question forbidden the direct calculation of 16 ^ 16.
  -- Define some variables according to the reference answer.
  let A : ℕ := (Nat.digits 10 (16 ^ 16)).sum
  let B : ℕ := (Nat.digits 10 A).sum
  let C : ℕ := (Nat.digits 10 B).sum
  -- We have C ≡ 7 [MOD 9].
  have h₀ : C ≡ 7 [MOD 9] := by
    calc
      C ≡ B [MOD 9] := by dsimp only [C]; symm; apply Nat.modEq_nine_digits_sum
      _ ≡ A [MOD 9] := by dsimp only [B]; symm; apply Nat.modEq_nine_digits_sum
      _ ≡ 16 ^ 16 [MOD 9] := by dsimp only [A]; symm; apply Nat.modEq_nine_digits_sum -- We use "dsimp only" to avoid calculating 16 ^ 16.
      _ ≡ (2 ^ 4) ^ 16 [MOD 9] := by congr
      _ ≡ 2 ^ 64 [MOD 9] := by rw [<-Nat.pow_mul]
      _ ≡ (2 ^ 6) ^ 10 * 2 ^ 4 [MOD 9] := by rw [<-Nat.pow_mul, <-Nat.pow_add]
      _ ≡ 1 ^ 10 * 2 ^ 4 [MOD 9] := by apply Nat.ModEq.mul_right; apply Nat.ModEq.pow; rw [Nat.modEq_iff_dvd]; norm_num
      _ ≡ 7 [MOD 9] := by rw [Nat.modEq_iff_dvd]; norm_num
  -- We have A ≤ 33 * 9. (Weaker than reference but enough.)
  have h₁ : 16 ^ 16 < 10 ^ 32 := by
    calc
      16 ^ 16 < (10 ^ 2) ^ 16 := by apply Nat.pow_lt_pow_left; norm_num; norm_num
      _ = 10 ^ 32 := by rw [<-Nat.pow_mul]
  replace h₁ : Nat.log 10 (16 ^ 16) ≤ 32 := by
    rw [<-@Nat.log_pow 10 (by norm_num) 32]
    apply Nat.log_mono_right
    apply le_of_lt h₁
  replace h₁ : (Nat.digits 10 (16 ^ 16)).length ≤ 33 := by
    rw [Nat.digits_len]
    linarith only [h₁]
    norm_num
    tauto
  replace h₁ : A ≤ 33 * 9 := by
    dsimp only [A]
    rw [<-List.map_id (Nat.digits 10 (16 ^ 16))]
    calc
      (List.map id (Nat.digits 10 (16 ^ 16))).sum ≤ (List.map (fun x => 9) (Nat.digits 10 (16 ^ 16))).sum := by apply List.sum_le_sum; simp only [id]; intro k hk; rw [<-Nat.lt_add_one_iff]; apply @Nat.digits_lt_base' 8 (16 ^ 16) k; exact hk
      _ = (Nat.digits 10 (16 ^ 16)).length * 9 := by rw [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
      _ ≤ 33 * 9 := by apply Nat.mul_le_mul_right; exact h₁
  -- Prove A ≠ 0 by proof by contradiciton.
  have h₂ : A ≠ 0 := by
    by_contra! this
    dsimp only [A] at this
    rw [List.sum_eq_zero_iff] at this
    -- To avoid the auto-unfold of 16 ^ 16.
    let n : ℕ := 16 ^ 16
    rw [show 16 ^ 16 = n by dsimp [n]] at this
    have weq : n = 0 := by
      calc
        n = Nat.ofDigits 10 (Nat.digits 10 n) := by rw [Nat.ofDigits_digits]
        _ = ∑ i : Fin (Nat.digits 10 n).length, 0 := by rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn]; rw [Finset.sum_congr]; rfl; simp (config := { dsimp := false }); intro x; specialize this ((Nat.digits 10 n)[↑x]); apply this; simp [List.getElem_mem]
        _ = 0 := by simp
    rw [show n = 16 ^ 16 by dsimp [n]] at weq
    linarith only [weq]
  -- We have B ≤ 3 * 9. (Weaker than reference but enough.)
  have h₃ : Nat.log 10 A < 3 := by
    apply Nat.log_lt_of_lt_pow
    exact h₂
    calc
      A ≤ 33 * 9 := h₁
      _ < 10 ^ 3 := by norm_num
  replace h₃ : (Nat.digits 10 A).length ≤ 3 := by
    rw [Nat.digits_len, Nat.add_one_le_iff]
    exact h₃
    norm_num
    exact h₂
  replace h₃ : B ≤ 3 * 9 := by
    dsimp only [B]
    rw [<-List.map_id (Nat.digits 10 A)]
    calc
      (List.map id (Nat.digits 10 A)).sum ≤ (List.map (fun x => 9) (Nat.digits 10 A)).sum := by apply List.sum_le_sum; simp only [id]; intro k hk; rw [<-Nat.lt_add_one_iff]; apply @Nat.digits_lt_base' 8 A k; exact hk
      _ = (Nat.digits 10 A).length * 9 := by rw [List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
      _ ≤ 3 * 9 := by apply Nat.mul_le_mul_right; exact h₃
  -- Prove B ≠ 0 by proof by contradiciton.
  have h₄ : B ≠ 0 := by
    by_contra! this
    dsimp only [B] at this
    rw [List.sum_eq_zero_iff] at this
    have weq : A = 0 := by
      calc
        A = Nat.ofDigits 10 (Nat.digits 10 A) := by rw [Nat.ofDigits_digits]
        _ = ∑ i : Fin (Nat.digits 10 A).length, 0 := by rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn]; rw [Finset.sum_congr]; rfl; simp; intro x; specialize this ((Nat.digits 10 A)[↑x]); apply this; simp [List.getElem_mem]
        _ = 0 := by simp
    tauto
  -- We have C ≤ 11. (Weaker than reference but enough.)
  have h₅ : Nat.log 10 B < 2 := by
    apply Nat.log_lt_of_lt_pow
    exact h₄
    calc
      B ≤ 3 * 9 := h₃
      _ < 10 ^ 2 := by norm_num
  replace h₅ : C ≤ 11 := by
    dsimp only [C]
    have h₅ : (Nat.digits 10 B).length ≤ 2 := by
      rw [show 2 = (Nat.digits 10 99).length by native_decide]
      apply Nat.le_digits_len_le
      omega
    let n : ℕ := (Nat.digits 10 B).length
    replace h₅ : n ≤ 2 := by
      dsimp [n]
      exact h₅
    have h₆ : (Nat.digits 10 B).length = n := by
      dsimp [n]
    -- Analyze three cases: 0 digit, 1 digit, 2 digits.
    interval_cases n
    . rw [List.length_eq_zero] at h₆
      rw [h₆, List.sum_nil]
      norm_num
    . rw [List.length_eq_one] at h₆
      obtain ⟨n₀, h₆⟩ := h₆
      rw [h₆, List.sum_singleton]
      suffices h₇ : n₀ < 10 by
        omega
      apply @Nat.digits_lt_base 10 B n₀
      norm_num
      rw [h₆]
      simp
    . rw [List.length_eq_two] at h₆
      obtain ⟨n₀, n₁, h₆⟩ := h₆
      rw [h₆]
      simp
      have h₇ : B = n₀ + n₁ * 10 := by
        rw [<-@Nat.ofDigits_digits 10 B, h₆, Nat.ofDigits_eq_sum_mapIdx]
        simp
      have h₇ : n₁ ≤ 2 := by
        omega
      have h₈ : n₀ < 10 := by
        apply @Nat.digits_lt_base 10 B n₀
        norm_num
        rw [h₆]
        simp
      omega
  calc
    (Nat.digits 10 (Nat.digits 10 (Nat.digits 10 (16 ^ 16)).sum).sum).sum = (Nat.digits 10 (Nat.digits 10 A).sum).sum := by dsimp only [A]
    _ = (Nat.digits 10 B).sum := by dsimp only [B]
    _ = C := by dsimp only [C]
    _ = 7 := by
      rw [Nat.modEq_iff_dvd, dvd_iff_exists_eq_mul_right] at h₀
      obtain ⟨c, h₀⟩ := h₀
      have h₆ : c = 0 := by
        omega
      rw [h₆] at h₀
      omega
