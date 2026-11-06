import Mathlib

/-Ken is the best sugar cube retailer in the nation. Trevor, who loves sugar, is coming over to make an order.
Ken knows Trevor cannot afford more than 127 sugar cubes, but might ask for any number of cubes less than or equal to that.
Ken prepares seven cups of cubes, with which he can satisfy any order Trevor might make. How many cubes are in the cup with the most sugar?-/
theorem number_theory_610891 (s : Finset ℕ) (hs : s = (Finset.range 7).image (fun i => 2 ^ i)) : ∀ a ≤ 127, ∃ A : Finset ℕ, A ⊆ s ∧ A.sum id = a := by
  -- The only way to fill seven cups to satisfy the above condition is to use a binary scheme, so the cups must contain $1,2,4,8,16,32$, and 64 cubes of sugar.
  have : ∀ n, ∀ a ≤ n, (∃ A : Finset ℕ, A ⊆ s ∧ A.sum id = a) ∨ 127 < a := by
    intro n
    induction n with
    | zero => simp ;use ∅ ;simp
    | succ d hd =>
      intro a ha
      by_cases h : a ≤ d
      · exact hd a h
      have ha : a = d + 1 := by linarith
      by_cases h : 127 < a ;simp [h]
      simp at h ;left
      have hm : ∃ m , 2 ^ m ≤ a ∧ a < 2 ^ (m + 1) := by
        refine exists_nat_pow_near (by rw [ha] ;simp) (by simp)
      rcases hm with ⟨m,hm⟩
      have h1 : a - 2 ^ m ≤ d := by
        rw [ha] ;refine Nat.sub_le_of_le_add ?_
        refine Nat.add_le_add (by simp) (Nat.one_le_two_pow)
      specialize hd (a - 2 ^ m) h1
      have h2 : ¬ 127 < a - 2 ^ m := by
        linarith
      simp [h2] at hd
      rcases hd with ⟨A,hA⟩
      use insert (2 ^ m) A
      constructor
      · refine Finset.insert_subset ?_ hA.1
        rw [hs] ;simp ;by_contra!
        have : 2 ^ 7 ≤ 2 ^ m := by apply Nat.pow_le_pow_of_le ;simp ;exact this
        linarith
      have : 2 ^ m ∉ A := by
        by_contra!
        have : ∑ x ∈ A, x = ∑ x ∈ A.erase (2 ^ m), x + 2 ^ m := by
          exact Eq.symm (Finset.sum_erase_add A (fun x ↦ x) this)
        rw [hA.2] at this
        have this' : 0 + 2 ^ m ≤ ∑ x ∈ A.erase (2 ^ m), x + 2 ^ m := by
          refine Nat.add_le_add ?_ (by simp)
          apply Finset.sum_nonneg
          intro i hi ;simp at hi
          have : i ∈ s := by exact hA.1 hi.2
          simp [hs] at this
          rcases this with ⟨j,hj⟩
          rw [← hj.2] ;exact Nat.zero_le (2 ^ j)
        rw [← this] at this'
        have : a - 2 ^ m < 2 ^ (m + 1) - 2 ^ m := by refine Nat.sub_lt_sub_right hm.1 hm.2
        rw [zero_add] at this' ;rw [pow_add,pow_one,mul_two] at this ;simp at this ;linarith
      rw [Finset.sum_insert this] ;simp [hA.2,ha] ;refine Nat.add_sub_of_le ?_
      rw [← ha] ;exact hm.1
  specialize this 127
  intro a ha
  rcases this a ha with this|this
  · exact this
  linarith