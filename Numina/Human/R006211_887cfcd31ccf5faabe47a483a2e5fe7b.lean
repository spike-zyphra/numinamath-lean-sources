import Mathlib

/-
Let $k$ be a positive integer. Calculate the sum $S_k = \sum_{j=1}^{23k} \lfloor \frac{17j}{23} \rfloor$. Show that $S_k = k \frac{391k - 5}{2}$.
-/

--We first simplify our expression.
lemma l1 (l : ℕ):
∑ x ∈ Finset.Icc (23*l+1) (23*(l+1)), ⌊17 * x / (23:ℝ)⌋ = 193 + 17 * 23 * l := by 
  --Move the interval.
  have t1 : ∑ x ∈ Finset.Icc (23*l+1) (23*(l+1)), ⌊17 * x / (23:ℝ)⌋ = ∑ i ∈ Finset.Icc (1:ℕ) 23, ⌊17 * (23*l + i) / (23:ℝ)⌋ := by 
    symm
    let f : ℕ → ℕ := fun i => 23*l + i
    apply Finset.sum_nbij
    have : ∀ a ∈ Finset.Icc 1 23, f a ∈ Finset.Icc (23 * l + 1) (23 * (l + 1)) := by 
      intro a ha
      simp at ha
      obtain ⟨al,au⟩ := ha
      simp [f]
      simp [al]
      ring_nf
      linarith
    exact this
    
    unfold Set.InjOn
    intro i1 hi1 i2 hi2 heq
    simp [f] at heq
    exact heq

    unfold Set.SurjOn
    intro i 
    simp [f]
    intro h1 h2
    have : 23 * (l + 1) = 23*l+23 := by ring
    rw [this] at h2
    tauto

    intro i hi
    simp at hi
    obtain ⟨il,iu⟩ := hi
    congr
    simp [f]
  --Take out the integers.
  have t2 : ∑ i ∈ Finset.Icc (1:ℕ) 23, ⌊17 * (23 * ↑l + ↑i) / (23:ℝ)⌋ = ∑ i ∈ Finset.Icc (1:ℕ) 23, ⌊17 * (↑i) / (23:ℝ)⌋ + 17 * 23 * l := by 
    have l1 : ∑ i ∈ Finset.Icc (1:ℕ) 23, ⌊17 * (23 * ↑l + ↑i) / (23:ℝ)⌋ = ∑ i ∈ Finset.Icc (1:ℕ) 23, (⌊17 * (↑i) / (23:ℝ)⌋ + 17 * l) := by
      refine Eq.symm (Finset.sum_congr rfl ?_)
      intro i hi; simp at hi
      obtain ⟨il,iu⟩ := hi
      ring_nf
      norm_cast
      exact Eq.symm (Int.floor_add_nat ((i:ℝ) * (17 / 23)) (l * 17))
    rw [l1]
    rw [Finset.sum_add_distrib]
    have l2 : ∑ x ∈ Finset.Icc 1 23, 17 * (l:ℤ) = 17 * (l:ℤ) * 23 := by simp; ring
    rw [l2]
    ring
  --Calculate the sum.
  have t3 : ∑ i ∈ Finset.Icc (1:ℕ) 23, ⌊17 * ↑i / (23:ℝ)⌋ =  193 := by 
    simp [Finset.sum_Icc_succ_top]
    norm_num
  
  simp [t1,t2,t3]

--Lemma 2 and 3 are about the intervals. Both are trivial.
lemma l2 (k : ℕ):
Finset.Icc 1 (23 * (k + 1)) = Finset.Icc 1 (23 * k) ∪ Finset.Icc (23 * k + 1) (23 * (k + 1)) := by 
  ext i
  simp

  constructor

  intro ⟨il,iu⟩ 
  by_cases h: i ≤ 23*k
  left
  tauto

  have : 23*k+1 ≤ i := by omega
  right
  tauto

  intro h
  rcases h with h|h
  omega
  omega
lemma l3 (k : ℕ):
Disjoint (Finset.Icc 1 (23 * k)) (Finset.Icc (23 * k + 1) (23 * (k + 1))) := by 
  intro S
  simp
  intro h1 h2
  ext i
  simp
  by_contra iinS
  have t1 := h1 iinS
  have t2 := h2 iinS
  simp at t1 t2
  omega

theorem number_theory_634693 (k : ℕ) (kpos : 0 < k) :
∑ j ∈ Finset.Icc (1) (23 * k), ⌊(17 * j / 23 : ℝ)⌋ = k * ((391 * k - 5) / (2:ℝ)) := by

  --We prove our claim by induction.
  induction' k with k hk

  --The base case is trivially by the first lemma.
  simp
  by_cases ke0 : k = 0
  simp [ke0]
  have t1:= by apply l1 0
  simp at t1 ⊢
  rify at t1
  field_simp at t1 ⊢
  rw [t1]
  norm_num

  --For the general case, we split the sum into two parts, then use the induction hypothesis and lemma 1 to calculate it.
  have : 0 < k := by omega
  simp [this] at hk
  simp
  have t1 := by apply l2 k
  rw [t1]
  rw [Finset.sum_union]
  rw [hk]
  have t2 := by apply l1 k
  rify at t2
  rw [t2]
  field_simp
  ring_nf
  apply l3 k