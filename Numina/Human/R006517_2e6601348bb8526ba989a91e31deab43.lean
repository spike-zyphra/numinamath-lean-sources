import Mathlib

/-
Let $n$ be an integer greater than or equal to 2. Let $a_1, a_2, \ldots, a_n$ be $n$ positive real numbers. Show that $\lfloor a_1 a_2 \dots a_n \rfloor \geq \lfloor a_1 \rfloor \lfloor a_2 \rfloor \dots \lfloor a_n \rfloor$.
-/


--We first show that the claim is true for n = 2.
lemma l1 (x y :ℝ) (xpos: 0 < x) (ypos: 0 < y):
  ⌊x⌋ * ⌊y⌋ ≤ ⌊x*y⌋ := by 
  
  refine Int.le_floor.mpr ?_
  push_cast
  gcongr
  exact Int.floor_le x
  exact Int.floor_le y

theorem number_theory_637950  (n : ℕ) (hn : 2 ≤ n) (a: ℕ → ℝ)  (ha : ∀ i ≥ 1, 0 < a i):
  ⌊∏ i ∈ Finset.Icc 1 n, a i⌋  ≥ ∏ i ∈ Finset.Icc 1 n, ⌊(a i)⌋ := by
  
  simp_all

  --The claim follows from the following simple induction.
  have cla : ∀m:ℕ, ∏ i ∈ Finset.Icc 1 (m+2), ⌊a i⌋ ≤ ⌊∏ i ∈ Finset.Icc 1 (m+2), a i⌋ := by 
    intro m
    induction' m with m hm

    --We have proved the case for n = 2.
    simp
    have : ∏ i ∈ Finset.Icc 1 2, ⌊a i⌋ = ⌊a 1⌋ * ⌊a 2⌋ := by
      rw [Finset.prod_Icc_succ_top (Nat.le.step Nat.le.refl) fun i => ⌊a i⌋]
      simp
    rw [this]
    have : ∏ x ∈ Finset.Icc 1 2, a x = a 1 * a 2 := by
      rw [Finset.prod_Icc_succ_top (Nat.le.step Nat.le.refl) a]
      simp
    rw [this]
    apply l1 (a 1) (a 2)
    apply ha; linarith;
    apply ha; linarith;

    --For general n, we simple apply the induction hypothesis and the case for n = 2.
    have t1 : ∏ i ∈ Finset.Icc 1 (m + 1 + 2), (⌊a i⌋)  = (∏ i ∈ Finset.Icc 1 (m + 2), (⌊a i⌋)) * ⌊a (m+2+1)⌋ := by
      have : m+1+2 = m+2+1 := by ring
      rw [this]
      refine Finset.prod_Icc_succ_top ?_ fun k => ⌊a k⌋
      linarith
    have t2 : ∏ i ∈ Finset.Icc 1 (m + 1 + 2), a i = (∏ i ∈ Finset.Icc 1 (m + 2), a i) * a (m+2+1) := by 
      have : m+1+2 = m+2+1 := by ring
      rw [this]
      refine Finset.prod_Icc_succ_top ?_ a
      linarith
    rw [t1,t2]
    
    have i1 :  (∏ i ∈ Finset.Icc 1 (m + 2), ⌊a i⌋) * ⌊a (m + 2 + 1)⌋ ≤ ⌊∏ i ∈ Finset.Icc 1 (m + 2), a i⌋ * ⌊a (m + 2 + 1)⌋ := by
      refine Int.mul_le_mul_of_nonneg_right hm ?_
      refine Int.floor_nonneg.mpr ?_
      specialize ha (m+2+1) (by linarith); linarith
    have i2 : ⌊∏ i ∈ Finset.Icc 1 (m + 2), a i⌋ * ⌊a (m + 2 + 1)⌋ ≤ ⌊(∏ i ∈ Finset.Icc 1 (m + 2), a i) * a (m + 2 + 1)⌋ := by 
      apply l1
      apply Finset.prod_pos
      simp
      intro i il iu
      apply ha; exact il
      apply ha; linarith;
    linarith




  have exi : ∃m:ℕ, m + 2 = n := by use n-2; omega
  obtain ⟨m,hm⟩ := exi
  specialize cla m
  rw [hm] at cla
  exact cla