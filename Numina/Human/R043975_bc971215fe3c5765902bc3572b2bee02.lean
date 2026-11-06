import Mathlib

/- Let $a$, $b$, $c$, and $d$ be real numbers with $|a-b|=2$, $|b-c|=3$, and $|c-d|=4$. What is the sum of all possible values of $|a-d|$? -/
theorem algebra_15245 (s : Set ℝ) (hs : s = {x : ℝ | ∃ a b c d : ℝ, |a - b| = 2 ∧ |b - c| = 3 ∧|c - d| = 4 ∧ x = |a - d|}) : ∑ᶠ x ∈ s, x = 18 := by

    --We firt prove that all possible values are 1,3,5,9.
    have smem: s = {1,3,5,9} := by 
      ext x
      constructor

      -- S ⊆ {1,3,5,9}. We prove this by enumerating the signs of a-b, b-c, c-d, and a-d.
      intro h
      simp; simp [hs] at h
      obtain ⟨a,b,h'⟩:= h
      obtain ⟨hab, h''⟩ := h'
      obtain ⟨c, h'''⟩:= h''
      obtain ⟨hbc, h'''⟩ := h'''
      obtain ⟨d, h''''⟩ := h'''
      obtain ⟨hcd, hadx⟩ := h''''

      have xnneg : 0 ≤ x := by rw [hadx]; exact abs_nonneg (a - d)
      have hab : a - b = 2 ∨ a - b = -2 := by exact eq_or_eq_neg_of_abs_eq hab
      have hbc : b - c = 3 ∨ b - c = -3 := by exact eq_or_eq_neg_of_abs_eq hbc
      have hcd : c - d = 4 ∨ c - d = -4 := by exact eq_or_eq_neg_of_abs_eq hcd
      have hadx: a - d = x ∨ a - d = -x := by symm at hadx; exact eq_or_eq_neg_of_abs_eq hadx

      cases hab
      cases hbc
      cases hcd
      cases hadx
      right;right;right; linarith
      exfalso; linarith
      cases hadx
      left; linarith
      exfalso; linarith
      cases hcd
      cases hadx
      right; left; linarith
      exfalso; linarith
      cases hadx
      exfalso; linarith
      right;right;left; linarith
      cases hbc
      cases hcd
      cases hadx
      right;right;left; linarith
      exfalso; linarith
      cases hadx
      exfalso; linarith
      right; left; linarith
      cases hcd
      cases hadx
      exfalso; linarith
      left; linarith
      cases hadx
      exfalso; linarith
      right;right;right; linarith
      
      -- {1,3,5,9} ⊆ s. We prove this by simply giving the value of a,b,c,d.
      simp
      intro h
      rcases h with h | h | h | h
      
      simp [h, hs]
      use 0, 2; simp
      use 5; norm_num
      use 1; norm_num

      simp [h, hs]
      use 0, 2; simp
      use -1; simp; norm_num
      use 3; simp; norm_num
      
      simp [h, hs]
      use 0, -2; simp
      use 1; norm_num
      use 5; simp; norm_num

      simp [h, hs]
      use 0, 2; simp
      use 5; norm_num
      use 9; norm_num


    --Then we simply calculate their sum by expanding the summation.
    let s1 : Set ℝ := {1,3}
    let s2 : Set ℝ := {5,9}

    have sui: s = s1 ∪ s2 := by
      simp [smem, s1, s2]
      ext x; simp; tauto
    rw [sui]  
    have : Disjoint s1 s2 := by 
      simp [s1,s2];
      unfold Disjoint
      intro X hX1 hX2;
      simp at hX1 hX2 ⊢
      ext x
      simp
      by_contra xinX
      have c1: x = 1 ∨ x = 3 := hX1 xinX
      have c2: x = 5 ∨ x = 9 := hX2 xinX
      rcases c1 with h1 | h1
      rcases c2 with h2 | h2
      linarith;linarith
      rcases c2 with h2 | h2
      linarith;linarith

    have : ∑ᶠ (x : ℝ) (_ : x ∈ s1 ∪ s2), x = (∑ᶠ (x : ℝ) (_ : x ∈ s1), x) + (∑ᶠ (x : ℝ) (_ : x ∈ s2), x) := by 
      apply finsum_mem_union
      assumption
      simp [s1]; simp [s2]
    rw [this]
    have : (∑ᶠ (x : ℝ) (_ : x ∈ s1), x) = 1 + 3 := by
      simp [s1];
      apply finsum_mem_pair; linarith
    ring_nf at this; rw [this]
    have : (∑ᶠ (x : ℝ) (_ : x ∈ s2), x) = 5 + 9 := by 
      simp [s2];
      apply finsum_mem_pair; linarith
    ring_nf at this; rw [this]
    norm_num
    