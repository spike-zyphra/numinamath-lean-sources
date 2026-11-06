import Mathlib

/- Find all the functions $f: \mathbb{N} \rightarrow \mathbb{N}$ such that:
$$
n+f(m) \mid f(n)+n f(m)
$$
for any $m, n \in \mathbb{N}$ -/
theorem number_theory_605311{f: ℕ → ℕ}:
  (∀m n, n + f m ∣ f n + n * f m) ↔
  ((f = fun n => n^2) ∨ (f = fun _ => 1) ∨ (f = fun _ => 0)) := by
  constructor
  · intro h
    -- from the given condition, we can prove n+fm ∣ fn - n^2
    have h1(m n: ℕ): (n + f m :ℤ) ∣ f n - n^2 := by
      have hh1: (f n + n * f m: ℤ) = (f n - n^2) + n * (n + f m) := by ring
      have hh2 := h m n
      zify at hh2; rw [hh1] at hh2
      apply (Int.dvd_iff_dvd_of_dvd_add hh2).mpr
      apply Int.dvd_mul_left
    -- therefore, fix n change m, n + f m ∣ f n - n^2 always holds.
    -- in other words, either fn - n^2 = 0, or n + f m is bounded.
    have h2: (∀n, f n = n^2) ∨ ∃N, ∀m, f m ≤ N := by
      by_cases hh: (∀n, f n = n^2)
      · left; exact hh
      push_neg at hh
      rcases hh with ⟨n, hn⟩
      -- if fn - n^2 ≠ 0 but n+fm ∣ f n - n^2, then n+fm ≤ fn - n^2 always hold.
      have(m:ℕ): (n + f m: ℤ) ≤ |(f n:ℤ) - n^2| := by
        apply Int.le_of_dvd
        · zify at hn
          exact abs_sub_pos.mpr hn
        · exact (dvd_abs _ _).mpr (h1 m n)
      -- thus we find an upperbound.
      right
      use ((f n: ℤ) - n^2).natAbs
      intro m; zify
      apply le_trans ?_ (this m)
      simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
    rcases h2 with inf_f | finite_f
    · left; funext n; rw [inf_f n]
    -- next, we consider range of f is finite case.
    -- suppose N is an upperbound.
    rcases finite_f with ⟨N, hN⟩
    -- from the given condition, we can prove n + fn ∣ (fn)^2 - fn
    have h2(n:ℕ): n + f n ∣ (f n)^2 - f n := by
      have hh1 := h n n
      have hh2: (f n + n * f n: ℤ) = (f n - (f n)^2) + (f n)*(n + f n) := by ring
      zify at hh1; rw [hh2] at hh1
      have hh3: (n + f n: ℤ) ∣ f n - (f n)^2 := by
        apply (Int.dvd_iff_dvd_of_dvd_add hh1).mpr
        apply Int.dvd_mul_left
      zify; rw [Nat.cast_sub, dvd_sub_comm]
      apply hh3
      rw [pow_two]; apply Nat.le_mul_self
    -- but fn^2 - fn is bounded by N^2 - N, while n+fn is unbounded.
    -- so must be the case right side fn^2 - fn = 0 for sufficiently large n.
    have h3: ∀n, n > N^2 → (f n) * (f n - 1) = 0 := by
      intro n hn
      by_contra!
      replace: 0 < (f n)^2 - f n := by
        rw [Nat.mul_sub, ← pow_two, mul_one] at this
        exact Nat.zero_lt_of_ne_zero this
      -- otherwise, by h2, we can prove n ≤ N^2, contradiction.
      have not_hn: n ≤ N^2 := calc
        n ≤ n + f n := by simp
        _ ≤ (f n)^2 - f n := Nat.le_of_dvd this (h2 n)
        _ ≤ (f n)^2 := by simp
        _ ≤ N^2 := Nat.pow_le_pow_of_le_left (hN n) 2
      linarith [hn, not_hn]
    -- choose sufficiently large n, observe behaviour of m and f(m).
    have h4(m:ℕ): f m = 1 ∨ f m = 0 := by
      -- fix m, take sufficiently large n (for example, N^2+1).
      have hh1 := h m (N^2+1)
      -- from h3, f (f - 1)=0, then f(N^2+1) = 0 or 1.
      obtain (f0 | f1): f (N^2+1) = 0 ∨ f (N^2+1) = 1 := by
        have := h3 (N^2+1) (by simp)
        rcases (mul_eq_zero.mp this) with f0 | f1
        · left; exact f0
        · have: f (N^2+1) ≤ 1 := by
            exact Nat.le_of_sub_eq_zero f1
          exact Nat.le_one_iff_eq_zero_or_eq_one.mp this
      · -- f (N^2+1) = 0 case.
        simp [f0] at hh1
        -- rearrange right side.
        have: (N^2+1)* f m = (N^2+1 + f m)*f m - (f m)^2 := by
          simp [Nat.add_mul, pow_two]
        rw [this] at hh1
        -- therefore N^2+1+fm ∣ fm^2
        replace: (N^2+1)+f m ∣ (f m)^2 := by
          have: (N^2+1) + f m ∣ (N^2+1+f m)* f m := by
            exact Nat.dvd_mul_right _ _
          zify; zify at this hh1
          rw [Nat.cast_sub (by nlinarith)] at hh1
          push_cast at hh1
          exact (Int.dvd_iff_dvd_of_dvd_sub hh1).mp this
        -- but it's impossible unless fm = 0, since N is an upperbound of f.
        by_cases hfm: f m = 0
        · right; exact hfm
        replace hfm: 0 < f m := by exact Nat.zero_lt_of_ne_zero hfm
        have hh2 := Nat.le_of_dvd (pow_pos hfm _) this
        have not_hh2: N^2+1+f m > (f m)^2 := by
          have: (f m)^2 ≤ N^2 := Nat.pow_le_pow_of_le_left (hN m) 2
          linarith [this]
        linarith [hh2, not_hh2]
      · -- f (N^2+1) = 1 case.
        simp [f1] at hh1
        zify at hh1
        -- rearrange right side.
        have: (1:ℤ) + (N^2+1)*f m = 1 - (f m)^2 + (f m)*((N^2+1)+f m) := by ring
        rw [this] at hh1
        -- consider value of fm.
        -- if f m = 0, done.
        by_cases hfm: f m = 0
        · right; exact hfm
        -- else fm^2 ≥ 1
        replace hfm: (f m)^2 ≥ 1 := by
          apply one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr hfm)
        -- therefore we obtain follow relation.
        have hh2: N^2+1 + f m ∣ (f m)^2 - 1 := by
          have: (N^2+1:ℤ) + f m ∣ 1 - (f m)^2 := by
            apply (Int.dvd_iff_dvd_of_dvd_add hh1).mpr
            exact Int.dvd_mul_left _ _
          zify; rw [dvd_sub_comm] at this
          rw [Nat.cast_sub hfm]
          exact this
        -- and then must be the case (fm)^2-1=0, otherwise left side ≤ right side, contradiction.
        have hh3: (f m)^2 - 1 = 0 := by
          by_contra!
          replace: 0 < (f m)^2 - 1 := Nat.zero_lt_of_ne_zero this
          replace hh2 := Nat.le_of_dvd this hh2
          have not_hh2: N^2+1+f m > (f m)^2 - 1 := calc
            N^2+1+f m ≥ (f m)^2 + 1 + f m := by
              have: N^2 ≥ (f m)^2 := Nat.pow_le_pow_of_le_left (hN m) _
              linarith [this]
            _ ≥ (f m)^2 + 1 := by simp
            _ > (f m)^2 := by simp
            _ ≥ _ := by simp
          linarith [hh2, not_hh2]
        -- therefore fm = 1
        simp [Nat.sub_eq_iff_eq_add' hfm] at hh3
        left; exact Nat.eq_one_of_mul_eq_one_left hh3
    -- combine h4 with h, we show f is either all 0 or all 1.
    replace h4: (∀m:ℕ, f m = 1) ∨ (∀m:ℕ, f m = 0) := by
      by_cases hf2: f 2 = 0
      · -- if f reach 0 at some points ≠ 0, then it's always 0.
        have: ∀n, n ∣ f n := by
          intro n
          have := h 2 n
          simp [hf2] at this
          exact this
        -- and we can prove f1 ≠ 1
        have f1_not1: f 1 ≠ 1 := by
          by_contra! hf1
          have := h1 1 2
          simp [hf2, hf1] at this
          norm_num at this
        -- impossible for n ∣ f n for any n, unless f n = 0.
        right; intro m
        by_cases hm0: m = 0
        · apply Nat.eq_zero_of_zero_dvd
          rw [hm0]; apply this 0
        by_cases hm1: m = 1
        · by_cases hfm: f m = 0
          · exact hfm
          · replace hfm: f m = 1 := by
              have := h4 m; tauto
            simp [hm1] at hfm
            contradiction
        have hm: m > 1 := by omega
        have: m ∣ f m := this m
        -- m ∣ f m and m > 1, this forces fm = 0
        by_contra! not_fm0
        replace not_fm0: 0 < f m := Nat.zero_lt_of_ne_zero not_fm0
        have not_hm := Nat.le_of_dvd not_fm0 this
        have fmeq1: f m = 1 := by
          have := h4 m
          simp [not_fm0.ne'] at this; exact this
        simp [fmeq1] at not_hm
        linarith [hm, not_hm]
      · push_neg at hf2
        replace hf2: f 2 = 1 := by
          have := h4 2
          tauto
        -- if f reach 1 at some points ≠ 1, then it's always 1.
        have hh1(n:ℕ): n + 1 ∣ n + f n := by
          have := h 2 n
          simp [hf2, add_comm _ n] at this
          exact this
        -- specially in this case, we can prove f0 ≠ 0.
        have f0_not0: f 0 ≠ 0 := by
          by_contra! f0_0
          have := h 0 2
          simp [hf2, f0_0] at this
        -- fn = 0 or 1 and n+1 ∣ n + fn forces fn take 1.
        left; intro n
        by_contra!
        replace: f n = 0 := by
          have := h4 n
          tauto
        have hh2: n+1 ∣ n := by
          have hh := hh1 n
          simp [this] at hh; exact hh
        have nnz: n ≠ 0 := by
          by_contra! hnz
          simp [hnz] at this
          contradiction
        -- impossible for n+1 divide n, given n ≠ 0.
        have: n+1 ≤ n := by
          apply Nat.le_of_dvd ?_ hh2
          exact Nat.zero_lt_of_ne_zero nnz
        simp at this
    -- done.
    right; rcases h4 with h41 | h40
    · left; funext n; apply h41 n
    · right; funext n; apply h40 n
  · -- verification
    rintro (hfn | (hf1 | hf0))
    · intro m n
      simp [hfn]
      have: n^2+n*m^2 = n * (n+m^2) := by ring
      exact Dvd.intro_left n this.symm
    · intro m n
      simp [hf1, add_comm _ 1]
    · intro m n
      simp [hf0]