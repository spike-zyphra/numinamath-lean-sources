import Mathlib

/-When working modulo $m$, the notation $a^{-1}$ is used to denote the residue $b$ for which $ab\equiv 1\pmod{m}$, if any exists. For how many integers $a$ satisfying $0 \le a < 100$ is it true that $a(a-1)^{-1} \equiv 4a^{-1} \pmod{20}$?-/
theorem number_theory_18579 :
    {a : ℕ | 0 ≤ a ∧ a < 100 ∧ ∃ x, a * x ≡ 1 [MOD 20] ∧ ∃ y, (a - 1) * y ≡ 1 [MOD 20] ∧ a * y ≡ 4 * x [MOD 20]} = ∅ := by
  -- show that the target is empty
  ext a
  simp
  intro ha x hxa y hya hxy
  -- divide into cases where 2 divides a or 2 divides a + 1
  have case_a : 2 ∣ a ∨ 2 ∣ a + 1 := by
    clear hxa hya hxy ha
    -- show the conclusion by induction
    induction a with
    | zero => simp -- when a = 0
    | succ a ha => -- when a satisfied
      cases ha with
      -- when a is even
      | inl h => right; simp [h]
      -- when a is odd
      | inr h => 
        left
        obtain ⟨k, hk⟩ := h
        use k
  -- divide into two possible cases
  cases case_a with
  -- when a is even
  | inl hda =>
    -- show that 2 ∣ a * x
    replace hda : 2 ∣ a * x := by
      obtain ⟨k, hk⟩ := hda
      use (k * x)
      rw [hk]
      ring_nf
    -- show that a * x ≡ 1 [MOD 20]
    replace hxa : a * x ≡ 1 [MOD 2 * 10] := by norm_num; exact hxa
    apply Nat.ModEq.of_mul_right at hxa
    -- contradiction with hda and hxa
    apply Dvd.dvd.modEq_zero_nat at hda
    have h : 0 ≡ 1 [MOD 2] := by
      calc
        0 ≡ a * x [MOD 2] := by exact hda.symm
        _ ≡ 1 [MOD 2] := by exact hxa
    contradiction
  -- when a is odd
  | inr hda =>
    -- show that 2 ∣ (a - 1) * y
    replace hda : 2 ∣ (a - 1) * y := by
      clear hxa hya ha hxy
      -- divide into cases that a = 0 or a > 0
      cases a with
      | zero => simp -- when a = 0
      | succ a => -- when a > 0
        obtain ⟨k, hk⟩ := hda
        use ((k - 1)* y)
        rw [Nat.add_sub_cancel]
        ring_nf at hk
        -- calculation that a * y = 2 * ((k - 1) * y)
        calc
          a * y = (a + 2 - 2) * y := by rw [Nat.add_sub_cancel]
          _ = (2 + a - 2) * y := by ring_nf
          _ = (k * 2 - 2) * y := by rw [hk]
          _ = (k * 2 - 1 * 2) * y := by ring_nf
          _ = (k - 1) * 2 * y := by rw [<-Nat.mul_sub_right_distrib]
          _ = 2 * ((k - 1) * y) := by ring_nf
    -- show that (a - 1) * y ≡ 1 [MOD 20]
    replace hya : (a - 1) * y ≡ 1 [MOD 2 * 10] := by norm_num; exact hya
    apply Nat.ModEq.of_mul_right at hya
    -- contradiction with hda and hya
    apply Dvd.dvd.modEq_zero_nat at hda
    have h : 0 ≡ 1 [MOD 2] := by
      calc
        0 ≡ (a - 1) * y [MOD 2] := by exact hda.symm
        _ ≡ 1 [MOD 2] := by exact hya
    contradiction