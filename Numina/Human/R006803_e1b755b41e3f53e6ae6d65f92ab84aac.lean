import Mathlib

/-
Theorem: Let $k$ be a natural number such that $k \ge 1$. Show that the sum of the integers from $(k-1)^2+1$ to $k^2$ inclusive is equal to $(k-1)^3 + k^3$.
-/

--Lemma about the sum of first n integers.
lemma squareSum (n:ℕ):
  ∑ i in Finset.Icc 0 n, (i:ℝ) = ((n:ℝ) * (n+1)) / 2 := by
  
  induction' n with n hn

  simp

  have eq: ∑ i ∈ Finset.Icc 0 (n + 1), (i:ℝ) = ∑ i in Finset.Icc 0 n, (i:ℝ) + ((n+1):ℝ) := by 
    rw [Finset.sum_Icc_succ_top]; 
    norm_cast; linarith
  rw [eq,hn]
  field_simp
  ring


theorem number_theory_641308 (k:ℕ) (hk: 1 ≤ k):
  ∑ i in Finset.Icc ((k - 1)^2 + 1) (k^2), i = (k - 1)^3 + k^3 := by


  --Note that [(k-1)^2+1, k^2] ∪ [0, (k-1)^2] = [0, k^2]. We apply the lemma twice.
  have eq : ∑ i in Finset.Icc 0 (k^2), (i:ℝ) = ∑ i in Finset.Icc 0 ((k-(1:ℕ))^2), (i:ℝ) + ∑ i in Finset.Icc ((k - (1:ℕ))^2 + 1) (k^2), (i:ℝ) := by 
    
    have t : Finset.Icc 0 (k^2) = Finset.Icc 0 ((k-1)^2) ∪ Finset.Icc ((k - 1)^2 + 1) (k^2) := by 
      ext i
      simp

      constructor

      intro h
      by_cases l : i ≤ (k - 1) ^ 2
      left; exact l
      right; push_neg at l
      constructor; linarith; linarith

      intro h
      rcases h with h | h
      have : (k-1)^2 ≤ k^2 := by 
        rify
        have : @Nat.cast ℝ AddMonoidWithOne.toNatCast (k - 1) = k-1 := by norm_cast
        rw [this]
        nlinarith
      linarith
      exact h.right
    rw [t]
    have d : Disjoint (Finset.Icc 0 ((k-1)^2)) (Finset.Icc ((k - 1)^2 + 1) (k^2)) := by 
      unfold Disjoint
      simp
      intro S h1 h2
      ext i
      simp
      by_contra iinS
      have i1 : i ∈ Finset.Icc 0 ((k - 1) ^ 2) := h1 iinS
      have i2 : i ∈ Finset.Icc ((k - 1) ^ 2 + 1) (k ^ 2) := h2 iinS
      simp at i1 i2
      obtain ⟨i2,_⟩ := i2
      linarith

    apply Finset.sum_union
    exact d
  
  have e1 : ∑ i in Finset.Icc 0 (k^2), (i:ℝ) =  ((k:ℝ)^2*(k^2+1))/2:= by rw [squareSum]; simp
  have e2 :  ∑ i in Finset.Icc 0 ((k-(1:ℕ))^2), (i:ℝ) =  ((k-1)^2 *((k-1)^2+1))/2 := by rw [squareSum]; norm_cast
  simp [e1,e2] at eq

  --Now the claim follows from simple calculation.
  rify
  have : @Nat.cast ℝ AddMonoidWithOne.toNatCast (k - 1) = (k-1) := by norm_cast
  rw [this]
  nlinarith
  
