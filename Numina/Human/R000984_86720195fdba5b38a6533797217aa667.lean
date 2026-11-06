import Mathlib

/- The first term of an arithmetic sequence is 1, another term of the sequence is 91 and all of the terms of the sequence are integers.
 How many distinct arithmetic sequences meet these three conditions? -/
theorem algebra_19582 :
    {(a, d) : ℤ × ℤ | a = 1 ∧ ∃ (n:ℕ), a + d * n = 91}.encard = 12 := by
  -- it suffices to find how many n divide 90
  -- 90 = 2 x 3^2x5, so factors of 90 are combination of 1,2,3,5.
  -- they are 2,3,5; 2x3, 2x5, 3x5, 3^2; 2x3^2, 3^2x5, 2x3x5; 1, 90
  have h1: ∀m:ℤ, 0 < m → m ≤ 90 → m ∣ 90 →
    (m=2 ∨ m=3 ∨ m=5 ∨ m=6 ∨ m=10 ∨ m=15 ∨ m=9 ∨
    m=18 ∨ m=45 ∨ m=30 ∨ m=1 ∨ m=90) := by decide
  have h2(d:ℤ){a:ℤ}(h: a=1 ∧ ∃(n:ℕ), a+d*n = 91): 0 < d ∧ d ≤ 90 ∧ d ∣ 90 := by
    have hh1: ∃(n:ℕ), d*n = 90 := by
      rcases h.right with ⟨m,hm⟩
      rw [h.left] at hm
      use m; linarith [hm]
    have hh2: 0 < d := by
      by_contra! hc
      rcases hh1 with ⟨n,hn⟩
      have: d*n ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg hc (by simp)
      rw [hn] at this; norm_num at this
    have hh3: d ∣ 90 := by
      rcases hh1 with ⟨n,hn⟩; rw [← hn]; use n
    have hh4: d ≤ 90 := by
      apply Int.le_of_dvd (by norm_num) hh3
    exact ⟨hh2,hh4,hh3⟩
  have h3{d:ℤ}(posd: 0 < d)(hdv: d ∣ 90): ∃n:ℕ, 1 + d*n = 91 := by
    rcases hdv with ⟨n,hn⟩
    use n.toNat
    have: d*n.toNat = 90 := by
      have: 0 ≤ n := by
        by_contra! hc
        have: d*n < 0 := by
          apply mul_neg_of_pos_of_neg posd hc
        rw [← hn] at this; norm_num at this
      rw [Int.toNat_of_nonneg this, hn]
    rw [this]; simp
  -- so the set just contain those factors
  have h4: {(a, d) : ℤ × ℤ | a = 1 ∧ ∃ (n:ℕ), a + d * n = 91} = {
    (1,2),(1,3),(1,5),(1,6),(1,10),(1,15),(1,9),
    (1,18),(1,45),(1,30),(1,1),(1,90)} := by
    ext ⟨a,d⟩
    simp; constructor <;> intro h
    · have hh1 := h.left
      have hh2 := h2 d h
      have hh3 := h1 d hh2.left hh2.right.left hh2.right.right
      tauto
    · have aeq: a = 1 := by tauto
      simp [aeq]
      rcases h with dd | dd | dd | dd | dd | dd | dd |
        dd | dd | dd | dd | dd
      <;> rw [dd.right]
      <;> apply h3
      all_goals norm_num
  -- so 12 elements in total.
  rw [h4]
  simp [Set.encard]
  rfl