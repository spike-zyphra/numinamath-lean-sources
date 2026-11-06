import Mathlib

-- Let ( n ) be a positive integer, and let ( a_1, a_2, \dots, a_n ) be a set of positive integers such that ( a_1 = 2 ) and ( a_m = \phi(a_{m+1}) ) for all ( 1 \leq m \leq n-1 ), where, for all positive integers ( k ), ( \phi(k) ) denotes the number of positive integers less than or equal to ( k ) that are relatively prime to ( k ). Prove that ( a_n \geq 2^{n-1} ).
theorem number_theory_608866 (n : ℕ) (hn : n > 1) (a : ℕ -> ℕ) (hpos : ∀ (m : ℕ), m > 0 ∧ m ≤ n -> a m > 0) (ha1 : a 1 = 2) (h : ∀ (m : ℕ), m > 0 ∧ m ≤ n-1 -> a m = (a (m+1)).totient) : a n ≥ 2 ^ (n-1) := by
  -- Step 1: Prove that for any `m > 1` and `m ≤ n`, `a m > 2`
  have hge : ∀ m, m > 1 ∧ m ≤ n -> a m > 2 := by
    intro m
    induction m with
    | zero =>
      -- Base case: `m = 0`, which is impossible due to the constraints
      intro hm
      linarith
    | succ m hm =>
      -- Inductive step: Consider `m + 1`
      by_cases hm' : m = 0
      · rw [hm']
        -- Case: `m = 0`, contradiction as `m > 1` is required
        intro hm
        linarith
      · by_cases hm'' : m = 1
        · rw [hm'']
          -- Case: `m = 1`, we use the definition of `a 1` and properties of the totient function
          simp
          intro hn'
          have : a 1 = (a 2).totient := by
            apply h 1 ⟨(by linarith), (Nat.le_sub_one_iff_lt (by linarith)).mpr hn'⟩
          rw [ha1] at this
          have ha2 : (a 2) ≥ 2 := by
            nth_rw 2 [this]
            apply Nat.totient_le
          nth_rw 1 [this]
          apply Nat.totient_lt
          linarith
        · -- General case: `m > 1`
          intro hmsucc
          have hm2 : m > 1 := by
            refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ?_
            simp
            exact ⟨hm', hm''⟩
          have hmn : m ≤ n := by linarith
          have hmgt:= hm ⟨hm2, hmn⟩
          have : a m = (a (m+1)).totient := by
            apply h m ⟨(by linarith), ?h⟩
            apply Nat.le_sub_of_add_le hmsucc.2
          have hmge := Nat.totient_le (a (m+1))
          linarith

  -- Step 2: Prove that 2 * m.totient ≤ m for even numbers
  have htotient : ∀ (m : ℕ), Even m -> 2 * m.totient ≤ m := by
    intro m hm
    by_cases hmzero : m = 0
    · rw [Nat.totient_eq_zero.mpr hmzero, hmzero]
    · have hmfac : ∃ m1, m = 2 ^ (m.factorization 2) * m1 := by
        refine exists_eq_mul_right_of_dvd ?h
        exact Nat.ord_proj_dvd m 2
      rcases hmfac with ⟨m1, heq⟩
      have hfacpos : m.factorization 2 > 0 := by
        apply Nat.Prime.factorization_pos_of_dvd (by norm_num) hmzero (even_iff_two_dvd.mp hm)
      have : ¬2 ^ (m.factorization 2 + 1) ∣ m := pow_succ_padicValNat_not_dvd hmzero
      have : m1.Coprime 2 := by
        nth_rw 2 [heq] at this
        have : ¬ 2 ∣ m1 := by
          intro hdvd
          have hfalse : 2 ^ (m.factorization 2 + 1) ∣ 2 ^ m.factorization 2 * m1 := by
            have eq: 2 ^ (m.factorization 2 + 1) = 2 ^ m.factorization 2 * 2 := by
              exact rfl
            rw [eq]
            exact Nat.mul_dvd_mul_left (2 ^ m.factorization 2) hdvd
          exact this hfalse
        refine Nat.coprime_two_right.mpr ?_
        refine Nat.odd_iff.mpr ?_
        exact Nat.two_dvd_ne_zero.mp this
      have : m1.Coprime (2 ^ (m.factorization 2)) := Nat.Coprime.pow_right (m.factorization 2) this
      rw [heq, Nat.totient_mul (Nat.coprime_comm.mp this)]
      rw [Nat.totient_prime_pow (by norm_num) hfacpos]
      simp
      group
      calc
        _ = m1.totient * (2 ^ (m.factorization 2 - 1) * 2) := by group
        _ = m1.totient * 2 ^ (m.factorization 2 -1 + 1) := rfl
        _ = m1.totient * 2 ^ (m.factorization 2) := by rw [Nat.sub_add_cancel hfacpos]
        _ ≤ _ := Nat.mul_le_mul_right (2 ^ m.factorization 2) (Nat.totient_le m1)

  -- Step 3: Prove that the totient of `a m` is even for `m > 2`
  have heven : ∀ m > 2, Even m.totient := by
    intro n
    apply Nat.totient_even

  -- Step 4: Prove that `a m` is even for all `m > 0` and `m ≤ n - 1`
  have h1 : ∀ m, m > 0 ∧ m ≤ n-1 -> Even (a m) := by
    intro m hm
    have := h m hm
    rw [this]
    apply heven
    apply hge
    constructor
    · linarith
    · apply Nat.add_le_of_le_sub (by linarith) hm.2

  -- Step 5: Prove that `a m ≥ 2 * a (m-1)` for `m > 1` and `m ≤ n - 1`
  have h2 : ∀ m, m > 1 ∧ m ≤ n-1 -> a (m) ≥ 2 * (a (m-1)) := by
    intro m hm
    have heq : a (m-1) = (a m ).totient := by
      have : m - 1 > 0 ∧ m - 1 ≤ n-1 := by
        constructor
        · apply Nat.zero_lt_sub_of_lt hm.1
        · calc
            _ ≤ n - 1 - 1:= by apply Nat.sub_le_sub_right hm.2 1
            _ ≤ _ := Nat.sub_le_succ_sub (n - 1) 1
      have := h (m-1) this
      have hmeq : m -1 + 1 = m := Nat.sub_add_cancel (by linarith)
      rw [hmeq] at this
      exact this
    have : Even (a m) := h1 m ⟨(by linarith), hm.2⟩
    have : 2 * (a m).totient ≤ a m := htotient (a m) this
    rw [← heq] at this
    exact this

  -- Step 6: Prove that `a m ≥ 2 ^ m` for all `m > 0` and `m ≤ n - 1`
  have h2pow : ∀ m, m > 0 ∧ m ≤ n-1 -> a m ≥ 2 ^ (m) := by
    intro m
    induction m with
    | zero =>
      intro hfalse
      linarith
    | succ m hm =>
      by_cases hmzero : m = 0
      · intro _
        rw [hmzero]
        simp
        linarith
      · intro hmsucc
        have : m > 0 ∧ m ≤ n-1:= by
          constructor
          · exact Nat.zero_lt_of_ne_zero hmzero
          · linarith
        have hmge := hm this
        have := h2 (m+1) ⟨(by linarith), hmsucc.2⟩
        simp at this
        calc
          _ ≥ 2 * a m := this
          _ ≥ 2 * 2 ^ m := by linarith
          _ = _ := by group

  -- Step 7: Combine results to conclude `a n ≥ 2 ^ (n-1)`
  have : a (n-1) ≥ 2 ^ (n-1) := by
    apply h2pow (n-1)
    constructor
    · exact Nat.zero_lt_sub_of_lt hn
    · linarith
  have hgen : a n ≥ a (n-1) := by
    have : a (n-1) = (a n).totient := by
      have han := h (n-1) ⟨Nat.zero_lt_sub_of_lt hn, (by linarith)⟩
      rw [han]
      have hneq : n - 1 + 1 = n := Nat.sub_add_cancel (by linarith)
      rw [hneq]
    rw [this]
    exact Nat.totient_le (a n)
  linarith
