import Mathlib

/-
N1. Find all pairs $(k, n)$ of positive integers for which $7^{k}-3^{n}$ divides $k^{4}+n^{2}$.
-/

-- These are two functions we will use later. We prove by induction some basic properties of them.
lemma hf1 (a:ℕ) (age4 : 4≤a):
0 < (7^(a)) - 8 * (a:ℤ)^4 := by
  
  have lem : ∀ n:ℕ, 0 < (7^(n+4)) - 8 * ((n:ℤ)+4)^4 := by 
    intro n
    induction' n with n hn

    simp

    have t0: 8 * ((n:ℤ) + 4) ^ 4 < (7:ℤ) ^ (n + 4) := by
      linarith
    have t1: (7:ℤ) ^ (n + 1 + 4) = 7 * 7 ^ (n + 4) := by 
      have : n + 1 + 4 = n + 4 + 1 := by ring
      rw [this]
      rw [pow_succ]
      ring
    have t2: 8 * (↑(n + 1) + 4) ^ 4 ≤ 7 * 8 * ((n:ℤ) + 4) ^ 4 := by
      norm_cast
      ring_nf
      nlinarith
    have t3: 0 ≤ 8 * ((n:ℤ) + 4) ^ 4 := by positivity
    have t4: 0 ≤ (7:ℤ) ^ (n + 4) := by positivity
    have : 8 * (↑(n + 1) + 4) ^ 4 < (7:ℤ) ^ (n + 1 + 4) := by linarith
    linarith

  have exi : ∃ n:ℕ, n + 4 = a := by use a - 4; omega
  obtain ⟨n,hn⟩ := exi
  have : @Nat.cast ℤ instNatCastInt a = (n:ℤ) + 4 := by rw [←hn]; norm_cast
  specialize lem n
  rw [hn] at lem
  rw [←this] at lem
  exact lem

lemma hf2 (b:ℕ):
0 < 3^b - 2*(b:ℤ)^2 := by 
  
  by_cases ble5 : b ≤ 5
  interval_cases b <;> simp
  push_neg at ble5

  induction' b with b hb

  simp

  by_cases bl5 : 5 < b 
  simp [bl5] at hb

  have t0: 2*((b:ℤ))^2 < 3^b := by linarith
  have t1: 3 ^ (b + 1) = (3:ℤ)*3^b := by
    rw [pow_succ]
    ring
  have t2: 2*(↑(b + 1))^2 ≤ 3*(2*(b:ℤ)^2) := by
    norm_cast
    ring_nf
    nlinarith
  have t4: 0 ≤ 2*((b:ℤ))^2 := by positivity
  have t5: (0:ℤ) ≤ 3^b := by positivity
  have : 2 * ↑(b + 1) ^ 2 < (3:ℤ) ^ (b + 1) := by linarith
  linarith

  have be5 : b = 5 := by omega
  simp [be5]

  
lemma hf3 (a:ℕ):
-400 < (7^(a)) - 8 * (a:ℤ)^4 := by 
  by_cases age4 : 4 ≤ a
  have : 0 < (7^(a)) - 8 * (a:ℤ)^4 := hf1 a age4
  linarith
  push_neg at age4
  interval_cases a <;> norm_num

lemma hf4 (b:ℕ) (bge6 : 6 ≤ b):
400 < 3^b - 2*(b:ℤ)^2 := by 
  have lem: ∀ n:ℕ, 400 < 3^(n+6) - 2*((n+6):ℤ)^2 := by 
    intro n
    induction' n with n hn

    simp

    have cla : 3 ^ (n + 6) - 2 * (↑n + 6) ^ 2 ≤ 3 ^ (n + 1 + 6) - 2 * (((n + 1):ℤ) + 6) ^ 2 := by 
      have t1 : 3 ^ (n + 1 + 6) = 3*3 ^ (n + 6) := by rw [pow_succ]; ring
      have t2 : 2 * (((n + 1):ℤ) + 6) ^ 2 ≤ 3*(2 * (↑n + 6) ^ 2) := by 
        norm_cast
        ring_nf
        omega
      nlinarith
    have : @Nat.cast ℤ instNatCastInt (n + 1) = n + 1 := by omega
    rw [this]
    linarith

  have exi: ∃n:ℕ, n + 6 = b := by use b - 6; omega
  obtain ⟨n,hn⟩ := exi
  specialize lem n
  have : @HAdd.hAdd ℤ ℤ ℤ instHAdd (↑n) 6 = @Nat.cast ℤ instNatCastInt b := by norm_cast
  rw [hn, this] at lem 
  exact lem



theorem number_theory_208738 (k n : ℕ) (kpos : 0 < k) (npos : 0 < n):
( ((7^k):ℤ) - 3^n ∣ k^4 + n^2) 
↔ 
k = 2 ∧ n = 4 := by

  constructor
  
  --From left to right.
  intro h
  --By parity check, we must have that both k and n are even.
  have eken : Even k ∧ Even n := by 

    have hk : Even k ∨ Odd k := by exact Nat.even_or_odd k
    have hn : Even n ∨ Odd n := by exact Nat.even_or_odd n

    rcases hk with evk | odk
    
    rcases hn with evn | odn
    tauto
    have e1 : Even (((7^k):ℤ) - 3^n ) := by 
      have : Odd (7:ℤ) := by use 3; norm_num
      have t1: Odd ((7^k):ℤ) := by exact Odd.pow this
      have : Odd (3:ℤ) := by use 1; norm_num
      have t2: Odd ((3^n):ℤ) := by exact Odd.pow this
      exact Odd.sub_odd t1 t2
    have e2 : Even (k^4 + (n:ℤ)^2) := by 
      exact Dvd.dvd.even h e1
    have o2 : Odd (k^4 + (n:ℤ)^2) := by 
      have t1 : Even ((k:ℤ)^4) := by 
        norm_cast
        refine Even.pow_of_ne_zero evk ?_
        linarith
      have t2 : Odd ((n:ℤ) ^ 2) := by 
        norm_cast
        exact Odd.pow odn
      exact Even.add_odd t1 t2
    have : ¬ Even (k^4 + (n:ℤ)^2) := by exact Int.not_even_iff_odd.mpr o2
    contradiction

    rcases hn with evn | odn
    have e1 : Even (((7^k):ℤ) - 3^n ) := by 
      have : Odd (7:ℤ) := by use 3; norm_num
      have t1: Odd ((7^k):ℤ) := by exact Odd.pow this
      have : Odd (3:ℤ) := by use 1; norm_num
      have t2: Odd ((3^n):ℤ) := by exact Odd.pow this
      exact Odd.sub_odd t1 t2
    have e2 : Even (k^4 + (n:ℤ)^2) := by 
      exact Dvd.dvd.even h e1
    have o2 : Odd (k^4 + (n:ℤ)^2) := by 
      have t1 : Odd ((k:ℤ)^4) := by 
        norm_cast
        exact Odd.pow odk
      have t2 : Even ((n:ℤ) ^ 2) := by 
        norm_cast
        refine (Nat.even_pow' ?_).mpr evn
        linarith
      exact Even.odd_add t2 t1
    have : ¬ Even (k^4 + (n:ℤ)^2) := by exact Int.not_even_iff_odd.mpr o2
    contradiction
    
    exfalso
    have t1 : 4 ∣ (7:ℤ)^k - 3^n := by
      have l1 : (7:ℤ) ≡ -1 [ZMOD 4] := by decide
      have l2 : (7:ℤ)^k ≡ (-1)^k [ZMOD 4] := by exact Int.ModEq.pow k l1
      have : (-1)^k = -1 := by exact Odd.neg_one_pow odk
      rw [this] at l2
      have l3 : (3:ℤ) ≡ -1 [ZMOD 4] := by decide
      have l4 : (3:ℤ)^n ≡ (-1)^n [ZMOD 4] := by exact Int.ModEq.pow n l3
      have : (-1)^n = -1 := by exact Odd.neg_one_pow odn
      rw [this] at l4
      have ee: (7:ℤ)^k - (3:ℤ)^n ≡ -1 - (-1) [ZMOD 4] := by exact Int.ModEq.sub l2 l4
      have : -1 - (-1) = 0 := by norm_num
      rw [this] at ee
      exact Int.dvd_of_emod_eq_zero ee
    have t2 : 4 ∣ k^4 + (n:ℤ)^2 := by exact Int.dvd_trans t1 h
    have t3 : 0 ≡ (k^4 + (n:ℤ)^2)  [ZMOD 4] := by symm; exact Int.ModEq.symm (Dvd.dvd.zero_modEq_int t2)
    have t4 : (k^4 + (n:ℤ)^2) ≡ 2 [ZMOD 4] := by 
      have l1: (k:ℤ)^4 ≡ 1 [ZMOD 4] := by 
        by_cases km0 : (k) % 4 = 0 
        have d4k : 4 ∣ k := by exact Nat.dvd_of_mod_eq_zero km0
        have evk : Even k := by 
          obtain ⟨d,hd⟩ := d4k
          use 2 * d
          omega
        have : ¬ Odd k := by exact Nat.not_odd_iff_even.mpr evk
        contradiction

        by_cases km1 : (k) % 4 = 1
        have : (k:ℤ) % 4 = 1 := by zify at km1; exact km1
        have : (k:ℤ) ≡ 1 [ZMOD 4] := by exact this
        have : (k:ℤ)^4 ≡ 1^4 [ZMOD 4] := by exact Int.ModEq.pow 4 this
        simp at this
        exact this
        by_cases km2 : (k) % 4 = 2 
        have d4km2 : 4 ∣ k - 2:= by 
          refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm km2))
          omega
        have evk : Even k := by 
          obtain ⟨d,hd⟩ := d4km2
          use (2*d+1)
          omega
        have : ¬ Odd k := by exact Nat.not_odd_iff_even.mpr evk
        contradiction
        
        have km3 : (k) % 4 = 3 := by omega
        have : (k:ℤ) ≡ 3 [ZMOD 4] := by zify at km3; exact km3
        have : (k:ℤ)^4 ≡ 3^4 [ZMOD 4] := by exact Int.ModEq.pow 4 this
        simp at this
        exact this

      have l2: (n:ℤ)^2 ≡ 1 [ZMOD 4] := by
        by_cases nm0 : (n) % 4 = 0 
        have d4n : 4 ∣ n := by exact Nat.dvd_of_mod_eq_zero nm0
        have evn : Even n := by 
          obtain ⟨d,hd⟩ := d4n
          use 2 * d
          omega
        have : ¬ Odd n := by exact Nat.not_odd_iff_even.mpr evn
        contradiction

        by_cases nm1 : (n) % 4 = 1
        have : (n:ℤ) % 4 = 1 := by zify at nm1; exact nm1
        have : (n:ℤ) ≡ 1 [ZMOD 4] := by exact this
        have : (n:ℤ)^2 ≡ 1^2 [ZMOD 4] := by exact Int.ModEq.pow 2 this
        simp at this
        exact this
        by_cases nm2 : (n) % 4 = 2 
        have d4nm2 : 4 ∣ n - 2:= by 
          refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm nm2))
          omega
        have evn : Even n := by 
          obtain ⟨d,hd⟩ := d4nm2
          use (2*d+1)
          omega
        have : ¬ Odd n := by exact Nat.not_odd_iff_even.mpr evn
        contradiction
        
        have nm3 : (n) % 4 = 3 := by omega
        have : (n:ℤ) ≡ 3 [ZMOD 4] := by zify at nm3; exact nm3
        have : (n:ℤ)^2 ≡ 3^2 [ZMOD 4] := by exact Int.ModEq.pow 2 this
        simp at this
        exact this
      have l3: (k^4 + (n:ℤ)^2) ≡ 1 + 1 [ZMOD 4] := by exact Int.ModEq.add l1 l2
      simp at l3
      exact l3
    have t5 : 0 ≡ 2 [ZMOD 4] := by exact Int.ModEq.trans t3 t4
    symm at t5
    have t6: (4:ℤ) ∣ 2 := by exact Int.dvd_of_emod_eq_zero t5
    norm_num at t6
    
  --Let k = 2a and n = 2b. Then, by assumption, we have 7^a + 3^b ∣ 8*a^4+2*b^2, so 7^a + 3^b ≤ 8 * a^4 + 2*b^2.
  obtain ⟨a,ha⟩ := eken.left
  obtain ⟨b,hb⟩ := eken.right

  have apos : 0 < a := by omega
  have bpos : 0 < b := by omega

  have cla : 7^a + 3^b ≤ 8 * a^4 + 2*b^2 := by

    have t1 : 7^a + 3^b ∣ 8 * a ^4 + 2*b^2 := by 
      zify
      obtain ⟨d,hd⟩ := h
      use (d*(7^a-3^b)/2)
      have e1 : (8 * (a:ℤ) ^ 4 + 2 * ↑b ^ 2)*2 = ↑k ^ 4 + ↑n ^ 2  := by 
        simp [ha,hb]
        ring
      have e2 : ((7 ^ a + 3 ^ b) * (d * (7 ^ a - 3 ^ b) / 2))*2 = (7 ^ k - 3 ^ n) * d := by 
        simp [ha,hb]
        rw [mul_assoc]
        have : (d * (7 ^ a - 3 ^ b) / 2) * 2 = d * (7 ^ a - 3 ^ b) := by 
          refine Int.ediv_two_mul_two_of_even ?_
          have : Even ((7:ℤ) ^ a - 3 ^ b) := by 
            have p1: Odd ((7:ℤ) ^ a) := by 
              have : Odd (7:ℤ) := by decide
              exact Odd.pow this
            have p2: Odd ((3:ℤ) ^ b) := by
              have : Odd (3:ℤ) := by decide
              exact Odd.pow this
            exact Odd.sub_odd p1 p2
          exact Even.mul_left this d
          
        rw [this]
        ring
      linarith

    apply Nat.le_of_dvd
    positivity; exact t1

  have age1 : 1 ≤ a := by 
    by_contra al1
    have ae0 : a = 0 := by exact Nat.eq_zero_of_not_pos al1
    simp [ae0] at ha
    linarith only [kpos,ha]
  have bge1 : 1 ≤ b := by 
    by_contra bl1
    have be0 : b = 0 := by exact Nat.eq_zero_of_not_pos bl1
    simp [be0] at hb
    linarith only [npos,hb]


  --Then, by the properties of f(x) = 7^x-x^4 and g(x)=3^x-x^2, we have that a ≤ 3 and b ≤ 5.
  have ale3 : a ≤ 3 := by 
    by_contra nale3
    have t1: 4 ≤ a := by omega
    apply hf1 at t1
    have t2: 0 < 3^b - 2*(b:ℤ)^2 := by apply hf2
    linarith

  have ble5 : b ≤ 5 := by 
    by_contra nble5
    have t1: 6 ≤ b := by omega
    apply hf4 at t1
    have t2: -400 < (7^(a)) - 8 * (a:ℤ)^4 := by apply hf3
    linarith

  --We just check every case.
  interval_cases a <;> 
  interval_cases b <;>
  simp_all <;>
  norm_num at h ⊢

  --From right to left, simple verification.
  intro ⟨ke,ne⟩
  simp [ke,ne]