import Mathlib

/-
Theorem: Let $N$ be a positive integer. Let $S$ be the total number of decimal digits required to write all natural numbers from 1 to $10^N$ inclusive. Show that $S = N \cdot 10^N - \sum_{i=0}^{N-1} 10^i + N+1$.
-/

--We first have a few trivial lemmas about exponents and intevals.
lemma l1 (n:ℕ): 10 ^ (n + 1) +1 ≤ 10 ^ (n + 1 + 1) - 1 := by 
  nth_rw 2 [pow_succ]
  have : 10 ≤ 10 ^ (n + 1) := by refine Nat.le_self_pow ?_ 10; omega
  omega

lemma l2 (n x :ℕ) (xl : 10 ^ (n + 1) + 1 ≤ x) (xu : x ≤ 10 ^ (n + 1 + 1) - 1): Nat.log 10 x = n + 1 := by
  rw [Nat.log_eq_iff]
  constructor
  linarith
  refine (Nat.le_sub_one_iff_lt ?_).mp xu
  exact Nat.pos_of_neZero (10 ^ (n + 1 + 1))
  left
  omega

lemma l3 (n : ℕ):
Finset.Icc 1 (10 ^ (n + 1 + 1)) = ( Finset.Icc 1 (10 ^ (n + 1)) ∪ Finset.Icc (10 ^ (n + 1)+1) (10^(n+1+1)-1) ∪ Finset.Icc (10 ^ (n + 1 + 1)) (10 ^ (n + 1 + 1)) ):= by 
  ext i;
  simp

  constructor
  
  intro h
  obtain ⟨il,ih⟩ := h
  
  by_cases h1 : i ≤ 10 ^ (n + 1)
  left
  tauto

  push_neg at h1
  have t1 : 10 ^ (n + 1) + 1 ≤ i := by exact h1

  by_cases h2 : i ≤ 10 ^ (n + 1 + 1) - 1
  right; left
  tauto

  have : i = 10 ^ (n + 1 + 1) := by omega
  right;right;
  exact this


  intro h
  rcases h with h | h | h

  obtain ⟨il,ih⟩ := h
  constructor
  exact il
  have : 10 ^ (n + 1) +1 ≤ 10 ^ (n + 1 + 1) - 1 := by apply l1
  omega

  obtain ⟨il, ih⟩ := h
  constructor
  have : 1 ≤ 10 ^ (n + 1) + 1  := by 
    have : 0 ≤ 10^(n+1) := by exact Nat.zero_le (10 ^ (n + 1))
    linarith
  linarith
  have : 10 ^ (n + 1 + 1) - 1 ≤ 10 ^ (n + 1 + 1)  := by exact Nat.sub_le (10 ^ (n + 1 + 1)) 1
  linarith

  constructor
  rw [h]; exact Nat.one_le_pow' (n + 1 + 1) 9
  rw [h];

lemma l4 (n:ℕ):
Disjoint (Finset.Icc 1 (10 ^ (n + 1))) (Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1)) := by 
  unfold Disjoint
  intro S
  simp
  intro h1 h2
  ext i
  simp
  by_contra iinS
  have t1 : i ∈ Finset.Icc 1 (10 ^ (n + 1)) := h1 iinS
  have t2 : i ∈ Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1) := h2 iinS
  simp at t1 t2
  linarith


lemma l5 (n:ℕ):
Disjoint (Finset.Icc 1 (10 ^ (n + 1)) ∪ Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1)) (Finset.Icc (10 ^ (n + 1 + 1)) (10 ^ (n + 1 + 1))) := by 
  unfold Disjoint
  intro S
  simp
  intro h1 h2
  rcases h2 with h2 | h2
  exact h2
  ext i
  simp
  by_contra iinS
  have t1 : i ∈ Finset.Icc 1 (10 ^ (n + 1)) ∪ Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1):= h1 iinS
  have t2 : i ∈ @singleton ℕ (Finset ℕ) Finset.instSingleton (10 ^ (n + 1 + 1)) := by rw [h2] at iinS; exact iinS
  simp at t1 t2
  rcases t1 with t1 | t1
  obtain ⟨_, t1 ⟩ := t1
  rw [t2] at t1
  have : 10 ^ (n + 1) < 10 ^ (n + 1 + 1) := by 
    have : 10 ^ (n + 1) +1 ≤ 10 ^ (n + 1 + 1) - 1 := by exact l1 n
    have : 10 ^ (n + 1) < 10 ^ (n + 1) +1 := by linarith
    have : 10 ^ (n + 1 + 1) - 1 ≤ 10 ^ (n + 1 + 1) := by exact Nat.sub_le (10 ^ (n + 1 + 1)) 1
    linarith
  linarith

  obtain ⟨_, t1⟩ := t1
  rw [t2] at t1
  have : 10 ^ (n + 1 + 1) - 1 < 10 ^ (n + 1 + 1) := by 
    refine Nat.sub_one_lt ?_
    exact Ne.symm (NeZero.ne' (10 ^ (n + 1 + 1)))
  linarith
  


theorem number_theory_635626 (N:ℕ) (hN: 0 < N):
∑ i ∈ Finset.Icc 1 (10^N), (Nat.digits 10 i).length = N * 10^N - ∑ i ∈ Finset.range N, 10^i + N + 1 := by

  --We prove our claim by induction on N
  have cla : ∀ n:ℕ, ∑ i ∈ Finset.Icc 1 (10^(n+1)), ((Nat.digits 10 i).length:ℤ) = (n+1) * 10^(n+1) - ∑ i ∈ Finset.range (n+1), 10^i + (n+1) + (1:ℤ) := by
    intro n

    induction' n with n hn

    --The base case is simple to check.
    simp; native_decide

    --For the induction, we apply our hypothesis and lemmas.
    have ll : 10 ^ (n + 1) +1 ≤ 10 ^ (n + 1 + 1) - 1 := by apply l1
    have lll: 10 ^ (n + 1) ≤ 10 ^ (n + 1 + 1) - 1 := by linarith [ll]
    
    --We decompose the interval into 3 parts and calculate each of them.
    have t : ∑ i ∈ Finset.Icc 1 (10 ^ (n + 1 + 1)), ((Nat.digits 10 i).length:ℤ) = ∑ i ∈ Finset.Icc 1 (10 ^ (n + 1)), ((Nat.digits 10 i).length:ℤ) + ∑ i ∈ Finset.Icc (10 ^ (n + 1)+1) (10^(n+1+1)-1), ((Nat.digits 10 i).length:ℤ) + ((Nat.digits 10 (10^(n+1+1))).length:ℤ) := by
      have : Finset.Icc 1 (10 ^ (n + 1 + 1)) = ( Finset.Icc 1 (10 ^ (n + 1)) ∪ Finset.Icc (10 ^ (n + 1)+1) (10^(n+1+1)-1) ∪ Finset.Icc (10 ^ (n + 1 + 1)) (10 ^ (n + 1 + 1)) ):= by apply l3
      rw [this]
      rw [Finset.sum_union]
      rw [Finset.sum_union]
      simp

      apply l4
      apply l5
    rw [t]

    have t2 : ∑ i ∈ Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1), ((Nat.digits 10 i).length:ℤ) = (n+2) * (10^(n+1+1)-1 - 10^(n+1)) := by 
      have l1 : ∑ i ∈ Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1), ((Nat.digits 10 i).length:ℤ) = ∑ i ∈ Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1), ((n:ℤ)+2) := by 
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp at hx
        obtain ⟨xl,xu⟩ := hx
        rw [Nat.digits_len]
        
        norm_cast
        simp
        apply l2
        exact xl
        exact xu


        linarith; norm_num; 
        have : 0 < x := by 
          have : 0 < 10^(n+1) + 1  := by positivity
          linarith
        linarith
      have l2 : ∑ i ∈ Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1), ((n:ℤ)+2) = (10^(n+1+1)-1 - 10^(n+1)) * (n+2):= by 
        rw [Finset.sum_const]
        have : (Finset.Icc (10 ^ (n + 1) + 1) (10 ^ (n + 1 + 1) - 1)).card = 10^(n+1+1)-1 - 10^(n+1) := by simp
        rw [this]

        have : @HSub.hSub ℕ ℕ ℕ instHSub (10 ^ (n + 1 + 1) - 1) (10 ^ (n + 1)) = @HSub.hSub ℤ ℤ ℤ instHSub (10 ^ (n + 1 + 1) - 1) (10 ^ (n + 1)) := by 
          have : @HSub.hSub ℤ ℤ ℤ instHSub (10 ^ (n + 1 + 1) - 1) (10 ^ (n + 1)) = Int.subNatNat (10 ^ (n + 1 + 1) - 1) (10 ^ (n + 1)) := by 
            rw [Int.subNatNat_of_le]
            field_simp
            exact lll
            
          rw [this]
          rw [Int.subNatNat_of_le]
          exact lll
          
        rw [← this]
        ring
      rw [l1,l2]
      ring



    have t3 : ((Nat.digits 10 (10 ^ (n + 1 + 1))).length:ℤ) = n+3 := by 
      rw [Nat.digits_len]
      norm_cast
      simp
      have : Nat.log 10 (10 ^ (n + 1 + 1)) = n + 1 + 1 := by rw [Nat.log_pow]; linarith
      rw [this]
      linarith
      exact Ne.symm (NeZero.ne' (10 ^ (n + 1 + 1)))
    have t4 : ∑ i ∈ Finset.range (n + 1 + 1), (10:ℤ) ^ i = ∑ i ∈ Finset.range (n + 1), 10 ^ i + 10 ^ (n + 1) := by
      apply Finset.sum_range_succ
    rw [hn, t2, t3, t4]
    field_simp
    ring_nf
    
    have : (n:ℤ) * 10 ^ n * 10 + 10 ^ n * 10 - ∑ x ∈ Finset.range (1 + n), 10 ^ x + (1 + ↑n) + 1 + (-2 - ↑n + ↑n * 10 ^ n * 90 + 10 ^ n * 180) + (3 + ↑n) = 100 * n * 10^n + 190 * 10^n + n + 3 - ∑ x ∈ Finset.range (1 + n), 10 ^ x := by ring
    rw [this]
    ring

  zify
  have exi : ∃ n:ℕ , n + 1 = N := by use N-1; omega
  obtain ⟨n,hn⟩ := exi;
  specialize cla n
  rw [hn] at cla
  zify at hn
  rw [hn] at cla

  have : @Nat.cast ℤ AddMonoidWithOne.toNatCast (N * 10 ^ N - ∑ i ∈ Finset.range N, 10 ^ i) = @HSub.hSub ℤ ℤ ℤ instHSub (↑N * 10 ^ N) (∑ i ∈ Finset.range N, 10 ^ i) := by 
    norm_cast
    refine Eq.symm (Int.subNatNat_of_le ?_)

    have t1 : ∑ i ∈ Finset.range N, 10 ^ i ≤ ∑ i ∈ Finset.range N, 10 ^ N := by 
      refine Finset.sum_le_sum ?_
      intro i hi
      simp at hi
      have : 10^i < 10^N := by refine (Nat.pow_lt_pow_iff_right ?_).mpr hi; norm_num
      linarith
    have t2 : ∑ i ∈ Finset.range N, (10 ^ N) = N * 10^N := by simp
    linarith
  
  rw [this]
  exact cla