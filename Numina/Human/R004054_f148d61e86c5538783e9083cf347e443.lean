import Mathlib

theorem algebra_234017 {a b S T: ℕ → ℝ}
  (a1 b1 da db: ℝ)
  (hS: ∀n, n > 0 → S n = ∑ i ∈ Finset.range n, a (i+1))
  (hT: ∀n, n > 0 → T n = ∑ i ∈ Finset.range n, b (i+1))
  (ha: ∀n, n > 0 → a n = a1 + (n-1) * da)
  (hb: ∀n, n > 0 → b n = b1 + (n-1) * db)
  (hST: ∀n, n > 0 → S n / T n = (3*n+2) / (2*n+1) ):
  a 7 / b 5 = 41 / 19 := by

  have sumeq {c1 d: ℝ} {n:ℕ}:
    ∑ i ∈ Finset.range (2*n+1), (c1 + i*d) =
      (2*n+1) * (c1 + n*d) := by
    induction' n with n ih
    · simp
    · have: 2*(n+1)+1 = (2*n+1) + 1 + 1 := by ring
      nth_rw 1 [this]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      push_cast
      ring

  have Seq (n:ℕ): S (2*n+1) = (2*n+1) * (a1 + n*da) := by
    rw [hS (2*n+1) (by simp)]
    replace ha (i:ℕ): a (i+1) = a1 + i*da := by simp [ha]
    simp only [ha]
    apply sumeq

  have Teq (n:ℕ): T (2*n+1) = (2*n+1) * (b1 + n*db) := by
    rw [hT (2*n+1) (by simp)]
    replace hb (i:ℕ): b (i+1) = b1 + i*db := by simp [hb]
    simp only [hb]
    apply sumeq

  replace hST (n:ℕ): S (2*n+1) / T (2*n+1) =
    (3*(2*n+1)+2) / (2*(2*n+1)+1) := by
    rw [hST (2*n+1) (by simp)]
    norm_cast

  replace hST (n:ℕ): (a1 + n*da) / (b1 + n*db) =
    (6*n+5) / (4*n+3) := by
    have: S (2*n+1) / T (2*n+1) =
      (a1 +n*da) / (b1 + n*db) := by
      rw [Seq, Teq]
      apply mul_div_mul_left _ _ ?_
      symm; apply ne_of_lt
      positivity
    rw [← this, hST]
    ring

  have hnz (n:ℕ): b1 + n*db ≠ 0 := by
    specialize hST n
    have h1: 0 < 4*n+3 := by positivity
    have h2: 0 < 6*n+5 := by positivity
    rintro heq
    simp only [heq, div_zero] at hST
    rify at h1 h2
    field_simp [h1.ne'] at hST
    simp [← hST] at h2

  replace hST (n:ℕ): a (n+1) / (6*n+5) = b (n+1) / (4*n+3) := by
    rw [ha (n+1) (by simp), hb (n+1) (by simp)]
    push_cast
    specialize hST n
    have h1: 0 < 4*n+3 := by positivity
    have h2: 0 < 6*n+5 := by positivity
    field_simp [hnz n] at hST
    field_simp [h1.ne', h2.ne']
    rwa [mul_comm _ (6*n+5:ℝ)]

  have ha1: a 1 = a1 := by simp [ha]
  have hb1: b 1 = b1 := by simp [hb]

  have eq1: a1 = 5/3 * b1 := by
    specialize hST 0
    norm_num at hST
    rw [ha1, hb1] at hST
    linarith only [hST]

  have eq2: a 2 = 11/7 * b 2 := by
    specialize hST 1
    norm_num at hST
    linarith only [hST]

  replace eq2: da = -2/21 * b1 + 11/7 * db := by
    rw [ha 2 (by norm_num), hb 2 (by norm_num)] at eq2
    norm_num at eq2
    linarith only [eq1, eq2]

  have eq3: a 3 = 17/11 * b 3 := by
    specialize hST 2
    norm_num at hST
    linarith only [hST]

  replace eq3: b1 = 3/4 * db := by
    have h1: a 3 = a1 + 2*da := by
      rw [ha 3 (by norm_num)]
      norm_num
    have h2: b 3 = b1 + 2*db := by
      rw [hb 3 (by norm_num)]
      norm_num
    rw [h1, h2, eq1, eq2] at eq3
    linarith only [eq3]

  replace eq2: da = 3/2 * db := by
    rw [eq2, eq3]
    ring

  replace eq1: a1 = 5/4 * db := by
    rw [eq1, eq3]
    ring

  replace hnz: db ≠ 0 := by
    specialize hnz 0
    simp only [eq3, CharP.cast_eq_zero, zero_mul, add_zero,
    ne_eq,  mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero,
    or_self, false_or] at hnz
    exact hnz

  rw [ha 7 (by norm_num), hb 5 (by norm_num), eq1, eq2, eq3]
  ring_nf
  simp [hnz]