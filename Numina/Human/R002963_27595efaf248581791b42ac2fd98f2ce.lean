import Mathlib

/- 43. In the city of Lisse, there are 10,000 telephones, the numbers of which are defined by four-digit numbers. In the central district, more than half of all telephones are installed. Prove that at least one of the central telephone numbers is equal to the sum of two other central telephone numbers (or double the number of such a telephone). -/



theorem number_theory_135922 (S : Set ℕ) (hS : S.ncard > 5000) (hS' : S ⊆ Set.Ico 0 10000) :
    ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x = y + z ∨ x = 2 * y := by
  -- let me be infimum of S, of course m belongs to S and for all element of S, m ≤ element
  let m := sInf S
  have h1 : (Set.Ico 0 10000).Finite := by
    exact Set.finite_Ico 0 10000
  have h2 : m ∈ S := Set.Nonempty.csInf_mem (Set.nonempty_of_ncard_ne_zero (by linarith)) (h1.subset hS')
  have h3 (x : ℕ) (h : x ∈ S) : m ≤ x := by apply Nat.sInf_le h
  -- consider S' created by subtracting m from all other elements of S
  let S' := (· - m) '' (S \ {m})
  -- S' ⊆ [0, 10000)
  have h4 : S' ⊆ Set.Ico 0 10000 := by
    rw [Set.subset_def]
    rintro x hx
    simp [S'] at hx
    obtain ⟨y, ⟨hyS, hym⟩, hy⟩ := hx
    simp
    have := Set.subset_def.mp hS' y hyS
    simp at this
    omega
  -- S ∪ S' is subset of [0, 10000) and S'.ncard ≥ 5000 as the function (· - m) is injective on S \ {m}
  have h5 : S ∪ S' ⊆ Set.Ico 0 10000 := Set.union_subset hS' h4
  have h6 : (S \ {m}).ncard ≥ 5000 := by
    rw [Set.ncard_diff]
    . simp
      omega
    . simpa
  have h7 : S'.ncard ≥ 5000 := by
    convert h6 using 1
    apply Set.ncard_image_of_injOn
    rintro a ha b hb hab
    simp at ha hb hab
    replace ha := h3 a ha.left
    replace hb := h3 b hb.left
    omega
  -- S and S' can't be distinct for their union would be larger than [0, 10000)
  have h8 : ¬ (Disjoint S S') := by
    by_contra h
    have h := Set.ncard_union_eq (s := S) (t := S') h ((Set.finite_Ico 0 10000).subset hS')
      ((Set.finite_Ico 0 10000).subset h4)
    have h' : (S ∪ S').ncard ≥ 10001 := by omega
    have h'' := Set.ncard_le_ncard h5
    rw [← Finset.coe_Ico, Set.ncard_coe_Finset] at h''
    simp at h''
    linarith
  -- let x belong to both S and S', then  z- m = x for some z in S, in particular z = m + x and we're done
  rw [Set.not_disjoint_iff] at h8
  obtain ⟨x, hSx, hS'x⟩ := h8
  simp [S'] at hS'x
  obtain ⟨z, ⟨hzS, hzm⟩, hz⟩ := hS'x
  replace hzS' := h3 z hzS
  use z, hzS, m, h2, x, hSx
  left
  omega