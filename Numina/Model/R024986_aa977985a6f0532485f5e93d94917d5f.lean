import Mathlib

open Finset Real

theorem algebra_239128 (a : ℕ → ℝ) (ha : ∀ i ∈ Icc 1 1990, 0 < a i)
    (M N : ℝ) (hM : M = (∑ i ∈ Icc 1 1989, a i) * (∑ i ∈ Icc 2 1990, a i))
    (hN : N = (∑ i ∈ Icc 1 1990, a i) * (∑ i ∈ Icc 2 1989, a i)) :
    M > N := by
  have h1 : (∑ i in Icc 1 1990, a i) = (∑ i in Icc 1 1989, a i) + a 1990 := by
    have h2 : (∑ i in Icc 1 1990, a i) = (∑ i in Icc 1 1989, a i) + a 1990 := by
      have h4 : (Icc (1 : ℕ) 1990 : Finset ℕ) = (Icc (1 : ℕ) 1989 : Finset ℕ) ∪ {1990} := by 
        ext x 
        simp 
        omega 
      have h5 : Disjoint (Icc (1 : ℕ) 1989 : Finset ℕ) ({1990} : Finset ℕ) := by 
        simp [disjoint_singleton_right]
      rw [h4]
      rw [sum_union h5]
      <;> simp [sum_singleton]
    linarith 
  have h2 : (∑ i in Icc 2 1990, a i) = (∑ i in Icc 2 1989, a i) + a 1990 := by
    have h3 : (∑ i in Icc 2 1990, a i) = (∑ i in Icc 2 1989, a i) + a 1990 := by
      have h4 : (Icc (2 : ℕ) 1990 : Finset ℕ) = (Icc (2 : ℕ) 1989 : Finset ℕ) ∪ {1990} := by 
        ext x 
        simp 
        omega 
      have h5 : Disjoint (Icc (2 : ℕ) 1989 : Finset ℕ) ({1990} : Finset ℕ) := by 
        simp [disjoint_singleton_right]
      rw [h4]
      rw [sum_union h5]
      <;> simp [sum_singleton]
    linarith 
  have h3 : (∑ i in Icc 1 1989, a i) = a 1 + (∑ i in Icc 2 1989, a i) := by 
    have h4 : (∑ i in Icc 1 1989, a i) = a 1 + (∑ i in Icc 2 1989, a i) := by 
      have h5 : (Icc (1 : ℕ) 1989 : Finset ℕ) = insert 1 (Icc (2 : ℕ) 1989 : Finset ℕ) := by 
        ext x 
        simp 
        omega 
      rw [h5] 
      rw [sum_insert (show (1 : ℕ) ∉ (Icc (2 : ℕ) 1989 : Finset ℕ) by 
        simp 
        <;> try { omega } 
      )]
      <;> try simp 
    linarith 
  rw [hM, hN]
  rw [h1, h2, h3]
  have ha1 : a 1 > 0 := by
    apply ha 1 
    norm_num 
  have ha1990 : a 1990 > 0 := by
    apply ha 1990 
    norm_num 
  have h4 : (a 1 + (∑ i in Icc 2 1989, a i)) * ((∑ i in Icc 2 1989, a i) + a 1990) - ((a 1 + (∑ i in Icc 2 1989, a i) + a 1990) * (∑ i in Icc 2 1989, a i)) = a 1 * a 1990 := by
    ring
  have h5 : (a 1 + (∑ i in Icc 2 1989, a i)) * ((∑ i in Icc 2 1989, a i) + a 1990) > ((a 1 + (∑ i in Icc 2 1989, a i) + a 1990) * (∑ i in Icc 2 1989, a i)) := by
    have h6 : ( (a 1 + (∑ i in Icc 2 1989, a i)) * ((∑ i in Icc 2 1989, a i) + a 1990) ) - ( (a 1 + (∑ i in Icc 2 1989, a i) + a 1990) * (∑ i in Icc 2 1989, a i) ) > 0 := by 
      rw [h4] 
      all_goals nlinarith 
    linarith 
  linarith