import Mathlib

/-
Let $N$ and $B$ be natural numbers. Let $a_k$ be a sequence of natural numbers defined by $a_k = 1$ if $k$ is odd, and $a_k = 0$ if $k$ is even.
Show that $(\sum_{k=0}^{N-1} a_k B^k) \pmod 2 = (B \pmod 2) \cdot (\lfloor N/2 \rfloor \pmod 2)$.
-/

theorem number_theory_637653 (N B : ℕ) (a: ℕ → ℕ) (ha : ∀ k: ℕ, (Odd k → a k = 1) ∧ (Even k → a k = 0) ):
(∑ k in Finset.range N, a k * B ^ k) % 2 = (B % 2) * (⌊(N / (2: ℝ))⌋ % 2)  := by
  --We prove it by induction on N.
  induction' N with N hN

  --For the base case, it is trivial by the assumption of a.
  simp
  by_cases Ne0 : N = 0
  simp [Ne0, ha]
  right
  norm_num
  have Nge1 : 1 ≤ N := by exact Nat.one_le_iff_ne_zero.mpr Ne0

  --For the general case, we apply the induction hypothesis and the assumption on a.
  rw [Finset.sum_range_succ]
  simp
  norm_cast at hN ⊢
  rw [Nat.add_mod]  
  push_cast at hN ⊢
  rw [hN]  
  field_simp
  ring_nf
  specialize ha N
  
  --If B is even, then B % 2 = 0 and the equation is trivially true.
  by_cases eB : Even B
  have : @HMod.hMod ℤ ℤ ℤ instHMod (↑B) 2 = 0 := by 
    norm_cast
    exact Nat.even_iff.mp eB
  simp [this]
  have : 2 ∣ B^N := by 
    refine Dvd.dvd.pow ?_ Ne0
    exact even_iff_two_dvd.mp eB
  norm_cast
  exact Dvd.dvd.mul_left this (a N)

  --Now, assume that B is odd.
  have oB : Odd B := by exact Nat.not_even_iff_odd.mp eB
  clear eB Ne0 hN
  have : B % 2 = 1 := by exact Nat.odd_iff.mp oB
  zify at this
  simp [this]
  clear this
  rw [@Int.emod_eq_emod_iff_emod_sub_eq_zero]
  rw [← @Int.even_iff]

  --There are 4 cases, depending on N % 4. We check every case separately and use the definition of a.
  by_cases m0 : N % 4 = 0
  have t1 : 4 ∣ N := by exact Nat.dvd_of_mod_eq_zero m0
  obtain ⟨d,hd⟩ := t1
  have eN : Even N := by use 2*d; simp [hd]; ring
  simp [eN] at ha
  simp [ha]
  have t2 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (↑N * 2⁻¹) = 2*d := by 
    simp [hd]; 
    ring_nf; 
    refine Int.floor_eq_iff.mpr ?_
    constructor
    norm_cast
    norm_cast
    omega
  have t3 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (2⁻¹ + ↑N * 2⁻¹)= 2*d := by
    simp [hd]
    ring_nf
    refine Int.floor_eq_iff.mpr ?_
    constructor
    norm_cast
    linarith
    simp
    rw [add_comm]
    gcongr
    norm_num
  rw [t2,t3]
  field_simp

  by_cases m1 : N % 4 = 1
  have t1 : 4 ∣ N - 1 := by exact (Nat.modEq_iff_dvd' Nge1).mp (id (Eq.symm m1))
  obtain ⟨d,hd⟩ := t1
  have oN : Odd N := by use 2*d; omega
  simp [oN] at ha
  simp [ha]
  have obn : Odd (@HPow.hPow ℤ ℕ ℤ instHPow (↑B) N ) := by 
    norm_cast
    exact Odd.pow oB
  have Ne : N = 4*d + 1 := by omega
  have t2 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (↑N * 2⁻¹) = 2*d := by 
    simp [Ne]
    ring_nf
    refine Int.floor_eq_iff.mpr ?_
    constructor
    norm_cast
    linarith
    rw [add_comm]
    refine add_lt_add_of_le_of_lt ?_ ?_
    norm_cast
    norm_num
  have t3 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (2⁻¹ + ↑N * 2⁻¹) = 2*d+1 := by 
    simp [Ne]
    ring_nf
    refine Int.floor_eq_iff.mpr ?_
    constructor
    norm_cast
    norm_cast
    linarith
  rw [t2,t3]
  field_simp
  have : Odd (1:ℤ) := by simp
  exact Odd.sub_odd obn this

  
  by_cases m2 : N % 4 = 2
  have t1 : 4 ∣ N - 2 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm m2)); omega
  obtain ⟨d,hd⟩ := t1
  have eN : Even N := by use 2*d+1; omega
  simp [eN] at ha
  simp [ha] 

  have Ne : N = 4*d + 2 := by omega
  have t2 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (↑N * 2⁻¹) = 2*d+1 := by 
    simp [Ne]
    ring_nf
    refine Int.floor_eq_iff.mpr ?_
    constructor
    norm_cast
    norm_cast
    linarith
  have t3 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (2⁻¹ + ↑N * 2⁻¹) = 2*d+1 := by 
    simp [Ne]
    ring_nf
    refine Int.floor_eq_iff.mpr ?_
    constructor
    simp
    norm_num
    simp
    ring_nf
    nlinarith
  rw [t2,t3]
  field_simp

  have m3 : N % 4 = 3 := by omega
  have t1 : 4 ∣ N - 3 := by refine (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm m3)); omega
  obtain ⟨d,hd⟩ := t1
  have oN : Odd N := by use 2*d+1; omega
  simp [oN] at ha
  simp [ha]
  have obn : Odd (B^N) := by
    refine Odd.pow oB
  
  have Ne : N = 4*d + 3 := by omega
  have t2 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (↑N * 2⁻¹) = 2*d + 1:= by 
    simp [Ne]
    ring_nf
    refine Int.floor_eq_iff.mpr ?_
    constructor
    norm_cast
    simp
    norm_num
    simp
    nlinarith
  have t3 : @Int.floor ℝ Real.instLinearOrderedRing Real.instFloorRing (2⁻¹ + ↑N * 2⁻¹) = 2*d + 2 := by 
    simp [Ne]
    ring_nf
    refine Int.floor_eq_iff.mpr ?_
    constructor
    norm_cast
    norm_cast
    omega
  simp [t2,t3]
  ring_nf
  refine Odd.add_odd ?_ ?_
  norm_cast
  norm_cast
  
  

  
  