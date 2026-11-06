import Mathlib

theorem number_theory_65992 :
    ¬∃ s1 s2 s3 : Finset ℕ,
      s1 ∪ s2 ∪ s3 = Finset.Icc 1 1998 ∧
      s1 ∩ s2 = ∅ ∧
      s1 ∩ s3 = ∅ ∧
      s2 ∩ s3 = ∅ ∧
      2000 ∣ ∑ x ∈ s1, x ∧
      3999 ∣ ∑ x ∈ s2, x ∧
      5998 ∣ ∑ x ∈ s3, x := by 
  rintro ⟨s1, s2, s3, h1, h2, h3, h4, h5, h6, h7⟩
  have h9 : ∑ x in s1, x + ∑ x in s2, x + ∑ x in s3, x = ∑ x in Finset.Icc 1 1998, x := by 
    have h10 : s1 ∪ s2 ∪ s3 = Finset.Icc 1 1998 := h1
    have h11 : s1 ∩ s2 = ∅ := h2
    have h12 : s1 ∩ s3 = ∅ := h3
    have h13 : s2 ∩ s3 = ∅ := h4
    have h14 : Disjoint s1 s2 := by 
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact h11
    have h15 : Disjoint s1 s3 := by 
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact h12
    have h16 : Disjoint s2 s3 := by 
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact h13
    calc
      ∑ x in s1, x + ∑ x in s2, x + ∑ x in s3, x = ∑ x in s1 ∪ s2, x + ∑ x in s3, x := by 
        rw [Finset.sum_union (show Disjoint s1 s2 by 
          exact h14
        )]
      _ = ∑ x in (s1 ∪ s2) ∪ s3, x := by 
        rw [Finset.sum_union (show Disjoint (s1 ∪ s2) s3 by 
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have hx5 : x ∈ s3 := hx2
          have hx3 : x ∈ s1 ∪ s2 := hx1
          simp at hx3
          rcases hx3 with (hx4 | hx4)
          · 
            have hx5 : x ∈ s1 := hx4
            have hx6 : x ∈ s3 := hx2
            have hx7 : x ∈ (s1 ∩ s3) := by 
              simp [hx5, hx6]
            have hx8 : (s1 ∩ s3) = ∅ := h12
            rw [hx8] at hx7
            simp at hx7
          · 
            have hx5 : x ∈ s2 := hx4
            have hx6 : x ∈ s3 := hx2
            have hx7 : x ∈ (s2 ∩ s3) := by 
              simp [hx5, hx6]
            have hx8 : (s2 ∩ s3) = ∅ := h13
            rw [hx8] at hx7
            simp at hx7
        )
      ]
      _ = ∑ x in Finset.Icc 1 1998, x := by 
        rw [show (s1 ∪ s2) ∪ s3 = Finset.Icc 1 1998 by 
          rw [show (s1 ∪ s2) ∪ s3 = s1 ∪ s2 ∪ s3 by 
            aesop
          ]
          rw [h10]
        ]
  have h13 : (∑ x in Finset.Icc 1 1998, x) = 1997001 := by
    native_decide
  have h14 : (∑ x in s1, x + ∑ x in s2, x + ∑ x in s3, x) = 1997001 := by
    linarith [h9, h13]
  omega