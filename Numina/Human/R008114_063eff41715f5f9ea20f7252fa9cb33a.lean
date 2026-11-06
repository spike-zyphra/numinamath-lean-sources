import Mathlib


theorem number_theory_128954 (n k : ℕ) (h : Odd k) :
    (∑ i ∈ Finset.Icc 1 n, i) ∣ (∑ i ∈  Finset.Icc 1 n, i ^ k) := by


  set N := (∑ i ∈  Finset.Icc 1 n, i ^ k) with hN1

  have heq {m:ℕ}: ∑ i ∈ Finset.Icc 1 m, i^k =
    ∑ i ∈ Finset.Icc 1 m, (m+1-i)^k := by
    by_cases hm: m = 0
    · simp [hm]
    replace hm: m ≥ 1 := by omega
    simp only [← Finset.sum_Ico_add_eq_sum_Icc hm]
    have: m ≤ (m+1)+1 := by omega
    have h1 := Finset.sum_Ico_reflect (fun x => x^k) 1 this
    replace: m+1+1-m = 1+1 := by omega
    simp only [this, add_tsub_cancel_right] at h1
    rw [h1, ← Finset.sum_Ico_add]
    have h2: (m+1-m)^k = 1 := by simp
    rw [h2, Finset.sum_Ico_add_eq_sum_Icc hm]
    clear * - hm
    induction' m,hm using Nat.le_induction with m hm ih
    · simp
    · rw [Finset.sum_Icc_succ_top (by simp), ih,
      Finset.sum_Ico_succ_top hm]
      ring


  have hN2: N = ∑ i ∈ Finset.Icc 1 n, (n+1-i)^k := by
    rw [hN1, heq]


  have eq1: 2*N = ∑ i ∈ Finset.Icc 1 n, ((n+1-i)^k + i^k) := by
    rw [Finset.sum_add_distrib, ← hN1, ← hN2, two_mul]

  have hdvd {i m:ℕ} (hi: i ∈ Finset.Icc 1 m):
    m+1 ∣ (m+1-i)^k + i^k := by
    replace hi: i ≤ m+1 := by
      simp only [Finset.mem_Icc] at hi
      linarith only [hi.right]
    zify
    rw [Nat.cast_sub hi]; push_cast
    have h1: m+1-i ≡ -i [ZMOD m+1] := Int.add_modEq_left
    have h2: (m+1-i:ℤ)^k ≡ (-i)^k [ZMOD m+1] := Int.ModEq.pow k h1
    rw [Odd.neg_pow h] at h2
    have h3: (m+1-i:ℤ)^k + i^k ≡ -i^k + i^k [ZMOD m+1] := by
      exact Int.ModEq.add h2 rfl
    simp only [neg_add_cancel] at h3
    exact Int.dvd_of_emod_eq_zero h3

  have n_add_1_dvd: n+1 ∣ 2*N := by
    rw [eq1]
    apply Finset.dvd_sum (fun _ hi => hdvd hi)

  have eq2 (hn: n ≥ 1): 2*N =
    2*n^k + ∑ i ∈ Finset.Icc 1 (n-1), ((n-i)^k+i^k) := by
    have: n-1+1 = n := by omega
    rw [Finset.sum_add_distrib]
    nth_rw 3 [← this]
    rw [← heq, hN1]
    nth_rw 1 [← this, Finset.sum_Icc_succ_top (by omega)]
    rw [this]
    ring

  have n_dvd (hn: n ≥ 1): n ∣ 2*N := by
    rw [eq2 hn]
    have h1: n ∣ 2*n^k := by
      apply Dvd.dvd.mul_left ?_ 2
      exact dvd_pow_self n (Nat.ne_of_odd_add h)
    have h2: n ∣ ∑ i ∈ Finset.Icc 1 (n-1), ((n-i)^k+i^k) := by
      apply Finset.dvd_sum (fun _ hi => ?_)
      have: n = n-1+1 := by omega
      rw [this]
      apply hdvd hi
    exact (Nat.dvd_add_iff_right h1).mp h2

  have eq3: (∑ i ∈ Finset.Icc 1 n, i) = (n+1)*n/2 := by
    have: ∑ i ∈ Finset.Icc 1 n, i = ∑ i ∈ Finset.range (n+1), i := by
      have: Finset.range (n + 1) = Finset.Icc 0 n := by
        ext n
        simp only [Finset.mem_range, Finset.mem_Icc, zero_le, true_and]
        omega
      rw [this]
      clear * -
      induction' n with n ih
      · simp
      · rw [Finset.sum_Icc_succ_top (by simp),
        Finset.sum_Icc_succ_top (by simp), ih]
    rw [this, Finset.sum_range_id, add_tsub_cancel_right]

  rw [eq3]

  by_cases hn: n = 0
  · simp [hn, hN1]
  replace hn: n ≥ 1 := by omega

  refine (Nat.div_dvd_iff_dvd_mul ?_ (by norm_num)).mpr ?_
  · refine even_iff_two_dvd.mp ?_
    rw [mul_comm]
    exact Nat.even_mul_succ_self _
  · refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ ?_
    · refine Nat.coprime_self_add_left.mpr ?_
      exact Nat.gcd_one_left n
    · exact n_add_1_dvd
    · exact n_dvd hn