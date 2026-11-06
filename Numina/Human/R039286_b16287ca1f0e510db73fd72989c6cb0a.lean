import Mathlib
/-- Call a positive integer $N$ a 7-10 double if the digits of the base-$7$ representation of $N$ form a base-$10$ number that is twice $N$. For example, $51$ is a 7-10 double because its base-$7$ representation is $102$. What is the largest 7-10 double? -/
theorem number_theory_97610 :
IsGreatest {N | 0 < N ∧ Nat.digits 7 N = (Nat.digits 10 (2 * N))} 315 := by
  constructor
  -- witness
  · simp only [Nat.reduceLeDiff, Set.mem_setOf_eq, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
    Nat.reduceMod, Nat.reduceDiv, Nat.mod_succ, Nat.digits_zero, Nat.reduceMul, and_self]
  -- upper bound
  · intros x hx
    simp only [Nat.reduceLeDiff, Set.mem_setOf_eq] at hx
    by_cases h : x ≤ 315
    · exact h
    have ha : 316 ≤ x := by linarith
    clear h
    obtain ⟨hx, hy⟩ := hx
    -- we will absolutely focus on the base 7 representation
    apply_fun (fun x => Nat.ofDigits 10 x) at hy
    rw [Nat.ofDigits_digits] at hy
    conv at hy =>
      right
      rw [←Nat.ofDigits_digits 7 x]
    -- lower bound on number of digits
    have al := Nat.le_digits_len_le 7 316 x ha
    rw [(by norm_num : (Nat.digits 7 316).length = 3)] at al
    obtain ⟨w, h⟩ : ∃ w, w = Nat.digits 7 x := ⟨_, rfl⟩
    -- get 3 digits
    cases' w with a w
    · rw [←h] at al; norm_num at al
    cases' w with b w
    · rw [←h] at al; norm_num at al
    cases' w with c w
    · rw [←h] at al; norm_num at al
    rw [←h] at hy
    simp only [Nat.ofDigits, Nat.cast_id] at hy
    have a9 := Nat.digits_lt_base (b := 7) (m := x) (d := a) (by norm_num) (by rw [←h]; simp only [List.mem_cons, true_or])
    have b9 := Nat.digits_lt_base (b := 7) (m := x) (d := b) (by norm_num) (by rw [←h]; simp only [List.mem_cons,
      true_or, or_true])
    have c9 := Nat.digits_lt_base (b := 7) (m := x) (d := c) (by norm_num) (by rw [←h]; simp only [List.mem_cons,
      true_or, or_true])
    ring_nf at hy
    have wx := @Nat.ofDigits_monotone 7 10 w (by norm_num)
    -- with omega we know that it only has exactly 3 digits
    have ww : Nat.ofDigits 7 w = 0 := by omega
    -- we definitively decompose x
    have zh : x = a + 7 * b + 49 * c := by
      apply_fun (fun x => Nat.ofDigits 7 x) at h
      rw [Nat.ofDigits_digits 7 x] at h
      simp only [Nat.ofDigits, Nat.cast_id] at h
      rw [ww] at h; rw [←h]
      ring
    rw [ww] at hy; norm_num at hy
    -- even when the base is different it is still zero
    have alz : Nat.ofDigits 10 w = 0 := by
      have jj := Nat.digits_zero_of_eq_zero (by norm_num) ww
      clear * - jj
      induction w with
      | nil => norm_num
      | cons he ta IH =>
        simp only [Nat.ofDigits, Nat.cast_id, List.mem_cons, true_or, jj, zero_add, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or]
        apply IH
        intros l hl
        apply jj
        simp only [List.mem_cons, hl, or_true]
    rw [alz] at hy; norm_num at hy
    -- conclude
    omega