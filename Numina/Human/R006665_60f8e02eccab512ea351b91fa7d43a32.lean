import Mathlib

/-
Let $N$ be an odd positive natural number. Let $a$ be a function from $\mathbb{Z}_N$ (the integers modulo $N$) to the set of natural numbers $\mathbb{N}$.
Theorem: There exists an element $i \in \mathbb{Z}_N$ such that the sum $a(i) + a(i+1)$ is an even number.
-/

theorem number_theory_639851 (N:ℕ) (hN: Odd N ∧ 0 < N) (a : (ZMod N) → ℕ):
  ∃i : ZMod N, Even (a i + a (i + 1)) := by

  --Wlog we can assume that a 0 is even, since otherwise we just consider a' i = 1 + a i.
  wlog ea0 : Even (a 0) 
  let a' : (ZMod N) → ℕ := fun x => (a x + 1)

  have tmp: ∃ i : ZMod N, Even (a' i + a' (i + 1)) := by
    apply this
    exact hN
    have : Odd (a 0) := by exact Nat.not_even_iff_odd.mp ea0
    simp [a']
    exact Odd.add_one this
  simp [a'] at tmp
  obtain ⟨i,hi⟩ := tmp
  obtain ⟨d,hd⟩ := hi
  use i
  use d - 1
  omega

  --Suppose the conclusion is not true.
  by_contra h
  push_neg at h

  --We have that even sum of consecutive pairs is odd.
  obtain ⟨oN,Npos⟩ := hN
  obtain ⟨k,hk⟩ := oN
  --We prove by induction that a N-1 has to be even, then a 0 and a N-1 form a contradiction to our assumption.
  have cla : Even (a (N-1)) := by 
    have tmp : ∀ i: ℕ, (Even i → Even (a i)) ∧ (Odd i → Odd (a i)) := by 
      intro i
      induction' i with i hi

      simp [ea0]

      by_cases ei : Even i
      simp [ei] at hi
      have oip1 : Odd (i+1) := by exact Even.add_one ei
      simp [oip1]
      by_contra con
      have : Even (a (↑i + 1)) := by exact Nat.not_odd_iff_even.mp con
      specialize h i
      have : Even (a i + a (i+1)) := by exact Even.add hi this
      contradiction

      have oi : Odd i := by exact Nat.not_even_iff_odd.mp ei
      simp [oi] at hi
      have eip1 : Even (i+1) := by exact Odd.add_one oi
      simp [eip1]
      by_contra con
      have : Odd (a (↑i + 1)) := by exact Nat.not_even_iff_odd.mp con
      specialize h i
      have : Even (a i + a (i+1)) := by exact Odd.add_odd hi this
      contradiction

    specialize tmp (N-1)
    have : Even (N-1) := by 
      use k
      omega
    simp [this] at tmp
    have : @Nat.cast (ZMod N) AddMonoidWithOne.toNatCast (N - 1) = @HSub.hSub (ZMod N) (ZMod N) (ZMod N) instHSub (↑N) 1 := by 
      simp; 
      rw [Nat.cast_pred Npos]
      simp
    rw [this] at tmp
    exact tmp

  specialize h (N-1)
  simp at h cla
  have : Even (a (-1) + a 0) := by exact Even.add cla ea0
  have :¬ Odd (a (-1) + a 0) := by exact Nat.not_odd_iff_even.mpr this
  contradiction

  