import Mathlib

/- Find the smallest positive real number $x$ such that
\[\lfloor x^2 \rfloor - x \lfloor x \rfloor = 6.\] -/
theorem algebra_14760 :
  IsLeast {x:ℝ | 0 < x ∧ ⌊x^2⌋ - x * ⌊x⌋ = 6} (55 / 7) := by
  rw [IsLeast, lowerBounds]; simp
  -- verify 55/7 satisfies is easy.
  constructor; norm_num
  -- and now, work on the hard direction.
  intro x hx h
  -- let n be integer part and f float part
  let n := ⌊x⌋
  have n_def: n = ⌊x⌋ := rfl
  let f := Int.fract x
  have f_def: f = Int.fract x := rfl
  have f_def': f = x-⌊x⌋ := by
    exact f_def
  have hfn: x = f+n := by
    symm; exact Int.fract_add_floor x
  -- notice that ⌊x^2⌋=⌊(n+f)^2⌋=⌊n^2+2nf+f^2⌋, since n is integer, so that equals n^2 + ⌊2nf+f^2⌋
  have h1: ⌊x^2⌋ = n^2+⌊2*n*f+f^2⌋ := by
    have ht1: x^2 = n^2+(2*n*f+f^2) := by
      rw [hfn]; ring
    rw [ht1, ← Int.floor_int_add]; simp
  -- x=n+f, so the equation turns to be n^2+⌊2nf+f^2⌋-n(n+f)=⌊2nf+f^2⌋-nf = 6
  have h2: ⌊x^2⌋ - x * ⌊x⌋ = ⌊2*n*f+f^2⌋-n*f := by
    rw [← n_def, h1, hfn]; simp; ring

  rw [h2] at h
  have h3: ⌊2*(n*f)+f^2⌋ = n*f+6 := by
    rw [← h]; ring_nf
  -- notice that left side of h3 is integer, therefore right side must be integer too. that's to say, nf is integer
  have h4: ∃a:ℤ, a = ↑n * f := by
    use (⌊2*(n*f)+f^2⌋-6)
    simp; rw [h3]; ring
  rcases h4 with ⟨nf, nfeq⟩
  -- nf is integer, so we can take nf out of floor.
  have h5: ⌊2*(n*f)+f^2⌋ = 2*(n*f) + ⌊f^2⌋ := by
    rw [← nfeq]
    have: 2*↑nf = (↑(2*nf):ℝ) := by simp
    rw [this, Int.floor_int_add]; simp
  -- so nf+f^2 = 6
  have eq1: n*f + ⌊f^2⌋ = 6 := by
    rw [h5] at h3; linarith [h3]
  -- f is fraction part of x < 1, so ⌊f^2⌋ = 0, and therefore nf=6, or f = 6/n
  have f_f: ⌊f^2⌋ = 0 := by
    have hh1: 0 ≤ f^2 := sq_nonneg f
    have hh2: |f| < 1 := by
      rw [f_def]
      apply abs_lt.mpr
      constructor
      · linarith [Int.fract_nonneg x]
      · exact Int.fract_lt_one x
    simp [hh1, hh2]
  have nnz: n ≠ 0 := by
    by_contra! hc
    rw [f_f, hc] at eq1; simp at eq1
  have eq2: f = 6/n := by
    rw [f_f] at eq1; simp at eq1
    rw [← eq1]
    field_simp [nnz]
  -- and n=6/f
  have eq3: n = 6/f := by
    rw [eq2]; field_simp [nnz]
  -- f is positive and less than 1, thus n > 6, or n ≥ 7.
  have nge: n ≥ 7 := by
    have ht1: 6/f > 6 := by
      have hh1: 0 < f := by
        by_cases hhf: f = 0
        · rw [f_f, hhf] at eq1; simp at eq1
        · have := Int.fract_nonneg x
          rw [← f_def] at this; push_neg at hhf
          apply lt_of_le_of_ne this hhf.symm
      have hh2: f < 1 := by
        exact Int.fract_lt_one x
      have hh3: 6 > f*6 := by linarith [hh1, hh2]
      -- should use lt_div_iff₀' in the new version lean4
      exact (lt_div_iff' hh1).mpr hh3
    have ht2: 0 < 6/f-6 := by linarith [ht1]
    have ht3: 0 < (n:ℝ)-6 := by
      rw [eq3]; apply ht2
    have ht4: 0 < n-6 := by
      have: 0 < (↑(n-6):ℝ) := by
        simp; linarith [ht3]
      apply Int.cast_pos.mp this
    linarith [ht4]
  -- when n=7, f=6/7, and x = 55/7
  by_cases neq: n = 7
  · rw [neq] at eq2; rw [neq] at hfn;
    rw [eq2] at hfn; rw [hfn]; simp; norm_num
  · -- when n=8, x ≥ 8 = 56/7 ≥ 55/7
    have hn1: n ≥ 8 := by
      push_neg at neq; exact lt_of_le_of_ne nge neq.symm
    have hn2: (n:ℝ) ≥ 8 := by
      apply Int.cast_le.mpr hn1
    have xge: x ≥ 8 := by
      have: x ≥ n := by
        rw [n_def]; exact Int.floor_le x
      apply le_trans hn2 this
    linarith