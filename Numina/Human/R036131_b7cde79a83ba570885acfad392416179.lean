import Mathlib


/- Compute the sum of all positive integers $n$ such that $n^{2}-3000$ is a perfect square. -/
theorem number_theory_610730:
  ∑ᶠ i ∈ {n:ℕ | IsSquare (n^2-3000) ∧ 0 < n^2 - 3000}, i = 1872 := by

  -- n^2 - 3000 is perfect square, or, n^2 - 3000 = k^2.
  -- then (n+k)(n-k) = 3000
  have h1 {n:ℕ} (hn: 0 < n^2-3000): IsSquare (n^2-3000) ↔ (∃ (k:ℕ), (n+k)*(n-k) = 3000) := by
    rw [isSquare_iff_exists_sq]
    replace hn: 3000 ≤ n^2 := (Nat.lt_of_sub_pos hn).le
    constructor <;> rintro ⟨k,hk⟩ <;> use k
    · rw [← Nat.sq_sub_sq]
      apply Nat.sub_eq_of_eq_add ?_
      apply (Nat.sub_eq_iff_eq_add' hn).mp hk
    · rw [← Nat.sq_sub_sq] at hk
      apply Nat.sub_eq_of_eq_add ?_
      refine (Nat.sub_eq_iff_eq_add' ?_).mp hk
      refine le_of_lt (Nat.lt_of_sub_pos ?_)
      norm_num [hk]

  -- consider factors of 3000.
  -- 3000 is even, so at least one of n+k, n-k is even.
  -- but n+k, n-k have same parity, so both be even.
  have even_add_sub {n k: ℕ} (h: 0 < n-k):
    Even (n+k) ↔ Even (n-k) := by
    rw [Nat.even_add]
    rw [Nat.even_sub (by omega)]

  -- therefore it suffices to consider (n'+k')n' = 750.
  have h2 {n k:ℕ} (h21: ∃ a, n+k = 2*a) (h22: ∃ b, n-k = 2*b)
    (hpos: 0 < n - k) (hk: (n+k)*(n-k) = 3000):
    ∃ (n' k':ℕ), (n'+k')*n' = 750 ∧ n = n' + (n'+k') := by
    rcases h21 with ⟨a,ha⟩
    rcases h22 with ⟨b,hb⟩
    use b,(a-b)
    have hba: 2*b ≤ 2*a := by
      rw [← hb, ← ha]
      simp [add_assoc]
    simp only [Nat.ofNat_pos, mul_le_mul_left] at hba
    constructor
    · rw [ha,hb] at hk
      replace hk: a*b = 750 := by
        linarith only [hk]
      simp [hba, hk]
    · have: 2*n = 2*(a+b) := by
        have: 2*n = (n+k) + (n-k) := by
          clear * - hpos
          omega
        rw [this, mul_add, ← ha, ← hb]
      simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at this
      rw [this]
      simp [hba, add_comm]

  replace h2 {n:ℕ} (h: ∃ (k:ℕ), (n+k)*(n-k) = 3000):
    ∃ (n' k':ℕ), (n'+k')*n' = 750 ∧ n = n' + (n'+k') := by
    rcases h with ⟨k,hk⟩
    have hpos: 0 < n-k := by
      by_contra!
      replace: n-k = 0 := Nat.eq_zero_of_le_zero this
      simp [this] at hk
    have: Even 3000 := Nat.even_iff.mpr rfl
    rw [← hk, Nat.even_mul] at this
    rcases this with h21 | h22
    · have h22 := (even_add_sub hpos).mp h21
      rw [even_iff_exists_two_mul] at h21 h22
      apply h2 h21 h22 hpos hk
    · have h21 := (even_add_sub hpos).mpr h22
      rw [even_iff_exists_two_mul] at h21 h22
      apply h2 h21 h22 hpos hk

  -- try some value, we find 27^2 < 750 < 28^2
  -- so if (n'+k') n' = 750, n' ≤ 27.
  have h3 {n' k':ℕ} (h: (n' + k')*n' = 750):
    n' ≤ 27 := by
    have hh1: (n'+k') * n' ≥ n'^2 := by
      rw [pow_two]
      apply Nat.mul_le_mul_right _ (by simp)
    -- if n' > 27, then n'^2 ≥ 28^2 > 750
    by_contra!
    replace: n' ≥ 28 := by exact this
    have hh2: n'^2 ≥ 28^2 := Nat.pow_le_pow_left this _
    rw [h] at hh1
    replace := hh2.trans hh1
    norm_num at this

  -- consider divisors of 750 ≤ 27.
  -- 750 = 2 x 3 x 5^3
  -- so they are 1,2,3,5, 2x3, 2x5, 3x5, 5x5.
  have h4: ∀n:ℕ, n ≤ 27 → n ∣ 750 → n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨
    n = 6 ∨ n = 10 ∨ n = 15 ∨ n = 25 := by
    decide


  -- and the other factor is 750, 375, 250, 150, 125, 75, 60, 30.
  -- so n is 752, 377, 253, 155, 131, 85, 65, 55
  have h5: {n:ℕ | IsSquare (n^2-3000) ∧ 0 < n^2 - 3000} =
    {1+750, 2+375, 3+250, 5+150, 6+125, 10+75, 15+50, 25+30} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, hpos⟩
      replace h := (h1 hpos).mp h
      obtain ⟨n',k',h,hn⟩ := h2 h
      rw [← h] at h4
      specialize h4 n' (h3 h) (Nat.dvd_mul_left n' (n' + k'))
      clear * - h h4 hn
      rcases h4 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        rw [hn]
        clear hn
        omega
    · clear * -
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals norm_num
      · use 749
      · use 373
      · use 247
      · use 145
      · use 119
      · use 65
      · use 35
      · use 5
  have: ({1+750, 2+375, 3+250, 5+150, 6+125, 10+75, 15+50, 25+30}: Set ℕ)
    = ↑ ({1+750, 2+375, 3+250, 5+150, 6+125, 10+75, 15+50, 25+30}: Finset ℕ) := by
    simp

  -- and their sum is 1872
  rw [h5, this]
  norm_cast
  rw [finsum_mem_finset_eq_sum]
  decide