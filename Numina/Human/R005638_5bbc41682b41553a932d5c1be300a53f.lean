import Mathlib

open Finset Real Nat

/-Let b(n) be the number of digits in the base -4 representation of n. Evaluate
(∑ i ∈  Icc 1 2013, b i) -/

/-- The number of digits in the base-4 representation of n. -/
def b (n : ℕ) : ℕ :=
  if n = 0 then 1 else log 4 n + 1

theorem number_theory_609209: (∑ i ∈  Icc 1 2013, b i) = 10719 := by
  -- Define the ranges and their corresponding digit counts --
  have h1 : ∀ i ∈ Finset.Icc 1 3, b i = 1 := by
    intro i hi
    simp at hi
    simp [b]
    omega

  have h2 : ∀ i ∈ Finset.Icc 4 15, b i = 2 := by
    intro i hi
    simp at hi
    simp [b]
    rcases hi with ⟨h1,h2⟩
    have o: i ≠ 0 := by omega
    simp [o]
    rw [Nat.log_eq_iff]
    simp
    omega
    left
    norm_num

  have h3 : ∀ i ∈ Finset.Icc 16 63, b i = 3 := by
    intro i hi
    simp at hi
    simp only [b]
    rcases hi with ⟨h1,h2⟩
    have o: i ≠ 0 := by omega
    simp [o]
    rw [Nat.log_eq_iff]
    simp
    omega
    left
    norm_num

  have h4 : ∀ i ∈ Finset.Icc 64 255, b i = 4 := by
    intro i hi
    simp at hi
    simp [b]
    rcases hi with ⟨h1,h2⟩
    have o: i ≠ 0 := by omega
    simp [o]
    rw [Nat.log_eq_iff]
    simp
    omega
    left
    norm_num

  have h5 : ∀ i ∈ Finset.Icc 256 1023, b i = 5 := by
    intro i hi
    simp at hi
    simp [b]
    rcases hi with ⟨h1,h2⟩
    have o: i ≠ 0 := by omega
    simp [o]
    rw [Nat.log_eq_iff]
    simp
    omega
    left
    norm_num

  have h6: ∀ i ∈ Finset.Icc 1024 2013, b i = 6 := by
    intro i hi
    simp at hi
    simp [b]
    rcases hi with ⟨h1,h2⟩
    have o: i ≠ 0 := by omega
    simp [o]
    rw [Nat.log_eq_iff]
    simp
    omega
    left
    norm_num

  have sum6: ∑ i ∈  Icc 1024 2013, b i = 5940 := by
    rw [Finset.sum_eq_card_nsmul h6]
    simp

  have eq6: (∑ i ∈  Icc 1 2013, b i)  = (∑ i ∈  Icc 1 1023, b i) + (∑ i ∈  Icc 1024 2013, b i) := by
    clear * -
    have h_disjoint : Disjoint (Icc 1 1023) (Icc 1024 2013) := by
      simp only [disjoint_iff_inter_eq_empty]
      ext x
      simp
      intro h g k
      linarith
    have h_union : Icc 1 1023 ∪ Icc 1024 2013 = Icc 1 2013 := by
      ext x
      simp only [mem_union, mem_Icc]
      constructor
      . intro h
        rcases h with h | h
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
      . intro h
        rcases h with ⟨h1, h2⟩
        simp [h1,h2]
        clear h1 h2
        by_contra! no
        rcases no with ⟨l1,l2⟩
        linarith
    rw [← h_union]
    set s1:= Icc 1 1023
    set s2:= Icc 1024 2013
    set s3:= Icc 1 2013
    clear_value s1 s2 s3
    apply Finset.sum_union h_disjoint

  rw [eq6,sum6]
  clear eq6 sum6 h6

  have sum5: ∑ i ∈  Icc 256 1023, b i = 3840 := by
    rw [Finset.sum_eq_card_nsmul h5]
    simp

  have eq5: (∑ i ∈  Icc 1 1023, b i)  = (∑ i ∈  Icc 1 255, b i) + (∑ i ∈  Icc 256 1023, b i) := by
    clear * -
    have h_disjoint : Disjoint (Icc 1 255) (Icc 256 1023) := by
      simp only [disjoint_iff_inter_eq_empty]
      ext x
      simp
      intro h g k
      linarith
    have h_union : Icc 1 255 ∪ Icc 256 1023 = Icc 1 1023 := by
      ext x
      simp only [mem_union, mem_Icc]
      constructor
      . intro h
        rcases h with h | h
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
      . intro h
        rcases h with ⟨h1, h2⟩
        simp [h1,h2]
        clear h1 h2
        omega
    rw [← h_union]
    set s1:= Icc 1 255
    set s2:= Icc 256 1023
    set s3:= Icc 1 1023
    clear_value s1 s2 s3
    apply Finset.sum_union h_disjoint

  rw [eq5,sum5]
  clear eq5 sum5 h5

  have sum4: ∑ i ∈  Icc 64 255, b i = 768 := by
    rw [Finset.sum_eq_card_nsmul h4]
    simp

  have eq4: (∑ i ∈  Icc 1 255, b i)  = (∑ i ∈  Icc 1 63, b i) + (∑ i ∈  Icc 64 255, b i) := by

    clear * -
    have h_disjoint : Disjoint (Icc 1 63) (Icc 64 255) := by
      simp only [disjoint_iff_inter_eq_empty]
      ext x
      simp
      intro h g k
      linarith
    have h_union : Icc 1 63 ∪ Icc 64 255 = Icc 1 255 := by
      ext x
      simp only [mem_union, mem_Icc]
      constructor
      . intro h
        rcases h with h | h
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
      . intro h
        rcases h with ⟨h1, h2⟩
        simp [h1,h2]
        clear h1 h2
        omega
    rw [← h_union]
    set s1:= Icc 1 63
    set s2:= Icc 64 255
    set s3:= Icc 1 255
    clear_value s1 s2 s3
    apply Finset.sum_union h_disjoint

  rw [eq4,sum4]
  clear eq4 sum4 h4

  have sum3: ∑ i ∈  Icc 16 63, b i = 144 := by
    rw [Finset.sum_eq_card_nsmul h3]
    simp

  have eq3: (∑ i ∈  Icc 1 63, b i)  = (∑ i ∈  Icc 1 15, b i) + (∑ i ∈  Icc 16 63, b i) := by
    clear * -
    have h_disjoint : Disjoint (Icc 1 15) (Icc 16 63) := by
      simp only [disjoint_iff_inter_eq_empty]
      ext x
      simp
      intro h g k
      linarith
    have h_union : Icc 1 15 ∪ Icc 16 63 = Icc 1 63 := by
      ext x
      simp only [mem_union, mem_Icc]
      constructor
      . intro h
        rcases h with h | h
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
      . intro h
        rcases h with ⟨h1, h2⟩
        simp [h1,h2]
        clear h1 h2
        omega
    rw [← h_union]
    set s1:= Icc 1 15
    set s2:= Icc 16 63
    set s3:= Icc 1 63
    clear_value s1 s2 s3
    apply Finset.sum_union h_disjoint

  rw [eq3,sum3]
  clear eq3 sum3 h3

  have sum2: ∑ i ∈  Icc 4 15, b i = 24 := by
    rw [Finset.sum_eq_card_nsmul h2]
    simp

  have eq2: (∑ i ∈  Icc 1 15, b i)  = (∑ i ∈  Icc 1 3, b i) + (∑ i ∈  Icc 4 15, b i) := by
    clear * -
    have h_disjoint : Disjoint (Icc 1 3) (Icc 4 15) := by
      simp only [disjoint_iff_inter_eq_empty]
      ext x
      simp
      intro h g k
      linarith
    have h_union : Icc 1 3 ∪ Icc 4 15 = Icc 1 15 := by
      ext x
      simp only [mem_union, mem_Icc]
      constructor
      . intro h
        rcases h with h | h
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
        . rcases h with ⟨h1, h2⟩
          constructor
          . linarith
          . linarith
      . intro h
        rcases h with ⟨h1, h2⟩
        simp [h1,h2]
        clear h1 h2
        omega
    rw [← h_union]
    set s1:= Icc 1 3
    set s2:= Icc 4 15
    set s3:= Icc 1 15
    clear_value s1 s2 s3
    apply Finset.sum_union h_disjoint

  rw [eq2,sum2]
  clear eq2 sum2 h2

  have sum1: ∑ i ∈  Icc 1 3, b i = 3 := by
    rw [Finset.sum_eq_card_nsmul h1]
    simp
  clear h1

  rw [sum1]