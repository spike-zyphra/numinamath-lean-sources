import Mathlib

/-Given that the sequence {a_n} is an arithmetic sequence with a common difference greater than 0,
and it satisfies a_3 * a_6 = 55 and a 2 + a 7 =16
(1) Find the general term formula of the sequence a n
(2) If the sequence a n and the sequence b n satisfy the equation a n =b1/2+b2/2^2+...+bn/2^n,
find the sum of the first n terms of the sequence b n, denoted as S n-/
theorem algebra_9768 {a b : ℕ → ℝ} (ha : ∃ d, (∀ n, a n = a 0 + d * n) ∧ (0 < d))
    (hb : ∀ n, a n = ∑ i ∈ Finset.Icc 1 n, b i / 2 ^ i)
    (h3 : a 3 * a 6 = 55) (h2 : a 2 + a 7 = 16) :
    (∀ n, a n = 2 * n - 1) ∧
    (∀ n, 1 ≤ n → ∑ i ∈ Finset.Icc 1 n, b i = 2 ^ (n + 2) - 6) := by
  -- Step 1: Prove the general term formula of the sequence a_n
  have h1: ∀ n, a n = 2 * n - 1 := by
    obtain ⟨d, h⟩:= ha
    rcases h with ⟨h,hd⟩
    have hd2:= h 2
    have hd3:= h 3
    have hd6:= h 6
    have hd7:= h 7
    simp [hd2,hd7] at h2
    simp [hd3,hd6] at h3
    ring_nf at h2 h3
    replace h2: a 0 = (16 - d * 9) / 2 := by
      field_simp
      linarith
    have h2':= h2
    simp [h2] at h3
    ring_nf at h3
    replace h2: d ^ 2 = 2 ^ 2 := by nlinarith
    rw [pow_eq_pow_iff_cases] at h2
    simp at h2
    have o: ¬ d = -2 := by
      by_contra! o
      rw [o] at hd
      absurd hd
      norm_num
    simp [o] at h2
    clear o
    simp [h2] at *
    norm_num at h2'
    intro n
    specialize h n
    simp [h2'] at h
    nlinarith
  -- Step 2: Prove the sum of the first n terms of the sequence b_n
  simp [h1]
  clear h2 h3 ha
  intro n
  induction' n with n hn
  . simp
  . by_cases i: n = 0
    . simp [i]
      specialize hb 1
      simp at hb
      specialize h1 1
      norm_num at h1
      linarith
    -- 1 ≤ n
    . replace i: 1 ≤ n := by omega
      simp [i] at hn
      simp
      rw [Finset.sum_Icc_succ_top]
      rw [hn]
      have f1:= hb n
      have f2:= hb (n + 1)
      have g1:= h1 n
      have g2:= h1 (n + 1)
      simp [g1,g2] at f1 f2
      clear * - f1 f2
      rw [Finset.sum_Icc_succ_top] at f2
      rw [← f1] at f2
      clear f1
      field_simp at f2
      replace f2: b (n + 1) = (2 * (↑n + 1) - 1) * 2 ^ (n + 1) - (2 * ↑n - 1) * 2 ^ (n + 1) := by nlinarith
      rw [f2]
      clear f2
      ring_nf
      omega
      omega