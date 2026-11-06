import Mathlib
/-- What is the largest even integer that cannot be written as the sum of two odd composite numbers? -/

theorem numbertheory_693 (a : ℕ) (hEven : Even a) (h : IsGreatest ({ a : ℕ | Even a ∧ ∀ (b c : ℕ) (hB : 1 < b) (hC : 1 < c) (hB2 : ¬ Nat.Prime b) (hC2 : ¬ Nat.Prime c) (hB3 : Odd b) (hC3 : Odd c), a ≠ b + c }) a) : a = 38 := by
  have saved := h
  have ste := Nat.mod_lt a (by decide : 6 > 0)
  have ad : ∀ x, x < 6 → x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 0 ∨ x = 2 ∨ x = 4 := by
    intros x y
    cases' x with x
    · decide
    cases' x with x
    · decide
    cases' x with x
    · decide
    cases' x with x
    · decide
    cases' x with x
    · decide
    cases' x with x
    · decide
    linarith
  obtain ⟨h1, h2⟩ := h

  have lwl : Even (6 * (a / 6)) := by
    rw [Nat.even_mul]
    left
    decide
  have bound : a < 44 := by
    rcases ad _ ste with h | ⟨h | ⟨h | ⟨h | ⟨h | h⟩⟩⟩⟩
    -- eliminate a % 6 = 1
    · rw [← Nat.div_add_mod a 6, h, Nat.even_add] at hEven
      rw [hEven] at lwl
      norm_num at lwl
    -- eliminate a % 6 = 3
    · rw [← Nat.div_add_mod a 6, h, Nat.even_add] at hEven
      rw [hEven] at lwl
      exfalso
      apply (by decide : ¬Even 3)
      assumption
    -- eliminate a % 6 = 5
    · rw [← Nat.div_add_mod a 6, h, Nat.even_add] at hEven
      rw [hEven] at lwl
      exfalso
      apply (by decide : ¬Even 5)
      assumption
    -- If $x \ge 18$ and is $0 \bmod{6}$, $x$ can be expressed as $9 + (9+6n)$ for some nonnegative $n$. Note that $9$ and $9+6n$ are both odd composites.
    · cases' (Classical.em (a < 18)) with hy hy
      · linarith
      cases' h1 with h11 h12
      have lad : ¬Nat.Prime (9 + 6 * ((a - 18) / 6)) := by
        rw [(by ring : 9 + 6 * ((a - 18) / 6) = 3 * (3 + 2 * ((a - 18) / 6)))]
        apply Nat.not_prime_mul
        · decide
        · intro as
          have := Nat.le_add_right 3 (2 * ((a - 18) / 6))
          rw [as] at this
          linarith
      have lwa : 9 ≤ 9 + 6 * ((a - 18) / 6) := by apply Nat.le_add_right
      have eij : Odd (9 + 6 * ((a - 18) / 6)) := by
        apply Even.odd_add
        · rw [Nat.even_mul]
          left
          decide
        · decide
      exfalso
      apply (h12 9 (9 + 6 * ((a - 18) / 6)) (by decide) (by linarith) (by decide) lad (by decide) eij)
      rw [(by linarith : 9 + (9 + 6 * ((a - 18) / 6)) = 18 + 6 * ((a - 18) / 6))]
      conv =>
        left
        rw [← @Nat.add_sub_of_le 18 a (by linarith), ← Nat.div_add_mod (a - 18) 6]
      rw [@Nat.sub_mod_eq_zero_of_mod_eq a 18 6 (by rw [h])]
      ring
    -- If $x\ge 44$ and is $2 \bmod{6}$, $x$ can be expressed as $35 + (9+6n)$ for some nonnegative $n$. Note that $35$ and $9+6n$ are both odd composites.
    · cases' (Classical.em (a < 44)) with hy hy
      · linarith
      cases' h1 with h11 h12
      have lad : ¬Nat.Prime (9 + 6 * ((a - 44) / 6)) := by
        rw [(by ring : 9 + 6 * ((a - 44) / 6) = 3 * (3 + 2 * ((a - 44) / 6)))]
        apply Nat.not_prime_mul
        · decide
        · intro as
          have := Nat.le_add_right 3 (2 * ((a - 44) / 6))
          rw [as] at this
          linarith
      have lwa : 9 ≤ 9 + 6 * ((a - 44) / 6) := by apply Nat.le_add_right
      have eij : Odd (9 + 6 * ((a - 44) / 6)) := by
        apply Even.odd_add
        · rw [Nat.even_mul]
          left
          decide
        · decide
      exfalso
      apply (h12 35 (9 + 6 * ((a - 44) / 6)) (by decide) (by linarith) (by decide) lad (by decide) eij)
      rw [(by linarith : 35 + (9 + 6 * ((a - 44) / 6)) = 44 + 6 * ((a - 44) / 6))]
      conv =>
        left
        rw [← @Nat.add_sub_of_le 44 a (by linarith), ← Nat.div_add_mod (a - 44) 6]
      rw [@Nat.sub_mod_eq_zero_of_mod_eq a 44 6 (by rw [h])]
      ring
    -- If $x\ge 34$ and is $4 \bmod{6}$, $x$ can be expressed as $25 + (9+6n)$ for some nonnegative $n$. Note that $25$ and $9+6n$ are both odd composites.
    · cases' (Classical.em (a < 34)) with hy hy
      · linarith
      cases' h1 with h11 h12
      have lad : ¬Nat.Prime (9 + 6 * ((a - 34) / 6)) := by
        rw [(by ring : 9 + 6 * ((a - 34) / 6) = 3 * (3 + 2 * ((a - 34) / 6)))]
        apply Nat.not_prime_mul
        · decide
        · intro as
          have := Nat.le_add_right 3 (2 * ((a - 34) / 6))
          rw [as] at this
          linarith
      have lwa : 9 ≤ 9 + 6 * ((a - 34) / 6) := by apply Nat.le_add_right
      have eij : Odd (9 + 6 * ((a - 34) / 6)) := by
        apply Even.odd_add
        · rw [Nat.even_mul]
          left
          decide
        · decide
      exfalso
      apply (h12 25 (9 + 6 * ((a - 34) / 6)) (by decide) (by linarith) (by decide) lad (by decide) eij)
      rw [(by linarith : 25 + (9 + 6 * ((a - 34) / 6)) = 34 + 6 * ((a - 34) / 6))]
      conv =>
        left
        rw [← @Nat.add_sub_of_le 34 a (by linarith), ← Nat.div_add_mod (a - 34) 6]
      rw [@Nat.sub_mod_eq_zero_of_mod_eq a 34 6 (by rw [h])]
      ring
  -- Now we've proved a < 44
  -- 43 is odd, goodbye
  cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ bound) with bound1 bound1
  · exfalso
    apply (by decide : ¬Even 43)
    rw [bound1] at h1
    tauto
  clear bound
  rename a < 43 => bound
  -- 42 = 9 + 33
  cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ bound) with bound1 bound1
  · exfalso
    apply h1.2 9 33 <;> try decide
    linarith
  clear bound
  rename a < 42 => bound
  -- 41 is odd, goodbye
  cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ bound) with bound1 bound1
  · exfalso
    apply (by decide : ¬Even 41)
    rw [bound1] at h1
    tauto
  clear bound
  rename a < 41 => bound
  -- 40 = 25 + 15
  cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ bound) with bound1 bound1
  · exfalso
    apply h1.2 25 15 <;> try decide
    linarith
  clear bound
  rename a < 40 => bound
  -- 39 is odd, goodbye
  cases' Nat.eq_or_lt_of_le (Nat.le_of_lt_succ bound) with bound1 bound1
  · exfalso
    apply (by decide : ¬Even 39)
    rw [bound1] at h1
    tauto
  clear bound
  apply (by apply Nat.le_antisymm; exact Nat.le_of_lt_succ bound1 : 38 ≤ a → a = 38)
  apply h2
  rw [Set.mem_setOf]
  constructor
  · decide
  intros b c hb hc pb pc ob oc heq
  symm at heq
  have bb := Nat.le.intro heq

  -- Algorithmically solve the goal by invoking decision procedures
  repeat (cases' Nat.eq_or_lt_of_le bb with bab bab; (· (have cab := Nat.eq_sub_of_add_eq' heq); rw [bab] at cab; norm_num at cab; (try have f1 : ¬ 1 < b := by (simp only [bab, cab]; decide)); (try have f2 : ¬ 1 < c := by (simp only [bab, cab]; decide)); (try have f3 : Nat.Prime b := by (simp only [bab, cab]; decide)); (try have f4 : Nat.Prime c := by (simp only [bab, cab]; decide)); (try have f5 : ¬ Odd b := by (simp only [bab, cab]; decide)); (try have f6 : ¬ Odd c := by (simp only [bab, cab]; decide)); tauto); clear bb; try have bb := Nat.le_of_lt_succ bab; clear bab)
  linarith