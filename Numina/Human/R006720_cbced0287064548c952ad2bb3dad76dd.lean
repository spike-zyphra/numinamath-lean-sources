import Mathlib
set_option maxHeartbeats 500000
set_option maxRecDepth 5000

/-
Prove that the number of distinct prime factors of 2^(2^m) - 1 is exactly m
under the assumption that all Fermat numbers F_i = 2^(2^i) + 1 for i < m are prime
-/
theorem fermat_number_prime_factors (m : ℕ)
    (h_fermat_primes : ∀ i < m, Nat.Prime (2^(2^i) + 1)) :
    (Nat.primeFactors (2^(2^m) - 1)).card = m:= by
  -- Inline definition of Fermat numbers
  set F : ℕ → ℕ := fun i => 2^(2^i) + 1

  -- Step 1: Prove the key identity ∀k, 2^(2^k) - 1 = ∏_{i=0}^{k-1} F_i
  -- This identity is fundamental for the factorization
  have key_identity : ∀ k, 2^(2^k) - 1 = ∏ i in Finset.range k, F i := by
    intro k
    induction k with
    | zero =>  -- For k=0: 2^1 - 1 = 1, empty product=1
      simp [Finset.range_zero, Finset.prod_empty]
    | succ k ih =>  -- Induction step
      rw [Finset.range_succ, Finset.prod_insert]
      rw [← ih, pow_succ, pow_mul, Nat.pow_two, ← Nat.sq_sub_sq]
      ring_nf
      simp

  -- Step 2: Prove Fermat numbers are pairwise coprime
  -- This is crucial for the prime factorization argument
  have pairwise_coprime : ∀ i j, i < m → j < m → i ≠ j →
      Nat.Coprime (F i) (F j) := by
    intro i j hi hj h_ne
    have h_ne':j≠i:=by exact id (Ne.symm h_ne)
    -- Without loss of generality, assume i < j
    wlog h_ij : i < j generalizing i j
    ·
      exact (Nat.Coprime.symm (this j i hj hi h_ne' h_ne (lt_of_le_of_ne (le_of_not_lt h_ij) h_ne')))

    -- Key identity: F_j - 2 = ∏_{t=0}^{j-1} F_t
    have fermat_diff : F j - 2 = ∏ t in Finset.range j, F t := by
      unfold F
      simp
      rw [key_identity j]

    -- Calculate gcd(F_i, F_j)
    have gcd_eq : Nat.gcd (F i) (F j) = Nat.gcd (F i) 2 := by
      set div := Nat.gcd (F i) (F j) with hdiv
      have t1 : div ∣ F j := Nat.gcd_dvd_right (F i) (F j)
      have t2 : div ∣ F j - 2 := by
        have i_in_range : i ∈ Finset.range j := Finset.mem_range.mpr h_ij
        rw [fermat_diff]
        have div_dvd_Fi : div ∣ F i := Nat.gcd_dvd_left (F i) (F j)
        apply Nat.dvd_trans div_dvd_Fi
        exact Finset.dvd_prod_of_mem F i_in_range

      have t3 : div ∣ F j - (F j - 2) := Nat.dvd_sub' t1 t2
      have t4 : F j ≥ 2 := by
        unfold F
        simp
        exact Nat.one_le_two_pow
      have t5 : F j - (F j - 2) = 2 := by omega
      rw [t5] at t3

      -- Since div divides 2 and F_i is odd, div must be 1
      have div_dvd_2 : div ∣ 2 := t3
      have odd_F : Odd (F i) := by
        unfold F
        simp [Nat.odd_add]
        refine (Nat.even_pow' ?_).mpr ?_
        simp;simp

      have t3:div∣(F j - (F j - 2)):=by exact Nat.dvd_sub' t1 t2
      have t4:F j>2:=by
        unfold F
        have t41:(2:ℕ)^j≥1:=by exact Nat.one_le_two_pow
        have helper_le {a b : ℕ} (h : 0 < b) : a ≤ a ^ b:=by
          refine (eq_zero_or_pos a).elim (by rintro rfl; simp) (fun ha => ?_)
          rw [(show b = b - 1 + 1 by omega), Nat.pow_succ]
          exact Nat.le_mul_of_pos_left _ (Nat.pow_pos ha)

        have t42:(2:ℕ)^2^j≥2:=by  exact helper_le t41
        exact Order.lt_add_one_iff.mpr t42
      have t5:(F j - (F j - 2))=2:=by omega
      rw [t5] at t3
      have t6:div=1∨div=2:=by refine (Nat.dvd_prime ?_).mp t3;exact Nat.prime_two
      have t7:div≤2:=by omega

      have gcd1:div=1:=by
        have t8:div∣(F i):=by exact Nat.gcd_dvd_left (F i) (F j)
        have t9:div∣2:=by exact t3
        have t10:¬(2:ℕ)∣(F i):=by
          simp
          unfold F
          have odd_F : Odd (F i) := by
            unfold F
            simp [Nat.odd_add]
            refine (Nat.even_pow' ?_).mpr ?_
            simp;simp
          exact Nat.odd_iff.mp odd_F
        have t11:div≠2:=by
          by_contra not
          rw [not] at t8
          contradiction
        omega
      rw [gcd1]
      exact Eq.symm ((fun {n} => Nat.coprime_two_right.mpr) odd_F)


    -- F_i is odd so gcd(F_i, 2) = 1
    have odd_F : Odd (F i) := by
      unfold F
      simp [Nat.odd_add]
      refine (Nat.even_pow' ?_).mpr ?_
      simp;simp
    have cop2:Nat.Coprime (F i) 2 :=by
      simp
      exact odd_F
    have gcd2:Nat.gcd (F i) 2 = 1:=by omega
    rw [gcd2] at gcd_eq
    omega

  -- Step 3: Combine results to count prime factors
  -- Decompose N using key identity
  have N_decomp : 2^(2^m) - 1 = ∏ i in Finset.range m, F i := key_identity m
  rw [N_decomp]

  -- Create set of primes
  let s := Finset.image F (Finset.range m)

  -- Prove all elements in s are prime
  have hs : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨i, hi, rfl⟩
    exact h_fermat_primes i (Finset.mem_range.1 hi)

  -- Prove product over range equals product over s
  have prod_eq : ∏ i ∈ Finset.range m, F i = ∏ p ∈ s, p := by
    refine Eq.symm (Finset.prod_image ?_)
    intro i hi j hj heq
    by_contra hne
    have cop := pairwise_coprime i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hne
    rw [heq] at cop
    have prime_i : Nat.Prime (F i) := h_fermat_primes i (Finset.mem_range.1 hi)
    have : F i = 1 := by
      rw [← Nat.gcd_self (F i), ← cop]
      simp
      omega
    have : F i ≥ 2 := Nat.Prime.two_le prime_i
    linarith

  -- Apply prime factors product theorem
  rw [prod_eq, Nat.primeFactors_prod hs]

  -- Calculate cardinality of s
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_range]  -- Range has exactly m elements
  · intro i hi j hj heq
    by_contra hne
    have cop := pairwise_coprime i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hne
    rw [heq] at cop
    have prime_i : Nat.Prime (F i) := h_fermat_primes i (Finset.mem_range.1 hi)
    have : F i = 1 := by
      rw [← Nat.gcd_self (F i), ← cop]
      simp
      omega
    have : F i ≥ 2 := Nat.Prime.two_le prime_i
    linarith
