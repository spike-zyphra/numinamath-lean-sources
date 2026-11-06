import Mathlib

/- Find all positive integers $n$ such that the decimal representation of $n^{2}$ consists of odd digits only. -/
theorem number_theory_604223 {n : ℕ}(npos: 0 < n) :
    (∀ d ∈ Nat.digits 10 (n ^ 2), Odd d) ↔ n = 1 ∨ n = 3 := by
  constructor
  · -- obviously, 10 is even
    have even10: Even 10 := by exact Nat.even_iff.mpr rfl
    -- last digits of n^2 is n^2 % 10
    have last_digit: n^2 % 10 ∈ Nat.digits 10 (n^2) := by aesop
    -- second last digit is n^2/10 % 10
    have second_last(hnsq: 0 < n^2/10): (n^2/10 % 10) ∈ Nat.digits 10 (n^2) := by
      rw [Nat.digits_of_two_le_of_pos (by norm_num) (Nat.pos_pow_of_pos 2 npos)]
      rw [Nat.digits_of_two_le_of_pos (by norm_num) hnsq]
      refine List.mem_cons_of_mem (n ^ 2 % 10) ?_
      exact List.mem_cons_self _ _
    intro h
    -- given digits of n^2 are odd, easy to verify n^2,n must be odd.
    have odd_nsq: Odd (n^2) := by
      replace := h (n^2 % 10) last_digit
      rw [← Nat.div_add_mod' (n^2) 10]
      apply Even.add_odd ?_ this
      apply Even.mul_left even10 _
    have oddn: Odd n := by
      exact Nat.Odd.of_mul_right odd_nsq
    -- n is odd, cannot be the case 10 ∣ n
    have not_10_dvd: ¬ 10 ∣ n := by
      rintro ⟨k, hk⟩
      simp [hk] at oddn
      absurd oddn
      refine Nat.not_odd_iff_even.mpr ?_
      exact Even.mul_right even10 k
    -- we only need consider n^2 > 10 case.
    -- because for n^2 ≤ 10, easy to verify only solution is 1,3, done.
    by_cases hnsq: n^2 ≤ 10
    · clear * - hnsq oddn
      have: n < 4 := by
        have: n^2 < 4^2 := by linarith [hnsq]
        exact lt_of_pow_lt_pow_left' 2 this
      replace: n ≤ 3 := by exact Nat.le_of_lt_succ this
      revert oddn hnsq
      revert n; decide
    push_neg at hnsq
    -- back to n^2 > 10 case.
    -- we claim n not divisible by 5.
    have not_5_dvd: ¬ 5 ∣ n := by
      -- otherwise, n = 10k + 5 for some k.
      by_contra!
      have: ∃k, n = 10*k + 5 := by
        use (n/10); rw [mul_comm 10 _]
        nth_rw 1 [← Nat.div_add_mod' n 10]
        congr
        omega
      rcases this with ⟨k, hk⟩
      -- easy to verify (10k+5)^2 = 100(k^2+k) + 25. so two last digits are 2,5.
      have nsq: n^2 = 100*(k^2+k) + 25 := by
        rw [hk]; ring
      -- second last digits is 2, even. contradiction.
      have h1: (n^2/10 % 10) ∈ Nat.digits 10 (n^2) := by
        apply second_last
        omega
      have h2: n^2 / 10 % 10 = 2 := by
        rw [nsq]
        omega
      rw [h2] at h1
      have h3 := h 2 h1
      absurd h3
      apply Nat.not_odd_iff.mpr rfl
    -- thus it simplifies to numbers of the form n = 10k +- m, where m = 1 or 3.
    have n_of_km: ∃ k:ℕ, ((n = 10*k + 1 ∨ n = 10*k - 1) ∨
      (n = 10*k + 3 ∨ n = 10*k - 3)) := by
      -- obviously, n = n/10 + last digits.
      have h1: n = n/10 * 10 + n % 10 := by
        symm; exact Nat.div_add_mod' n 10
      -- n is odd, so n % 10 can only be 1,3,5,7,9.
      have h2: n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 5 ∨ n % 10 = 7 ∨ n % 10 = 9 := by
        have hh1: Odd (n % 10) := Odd.mod_even oddn even10
        have hh2: ∀m:ℕ, m < 10 → Odd m → m = 1 ∨ m = 3 ∨ m = 5 ∨
          m = 7 ∨ m = 9 := by decide
        apply hh2 _ ?_ hh1
        apply Nat.mod_lt n (by norm_num)
      -- n not divided by 5, so n % 10 cannot be 5
      have h3: n % 10 ≠ 5 := by
        contrapose! not_5_dvd
        rw [h1, not_5_dvd]
        refine Nat.dvd_add_self_right.mpr ?_
        apply Dvd.dvd.mul_left (by norm_num)
      -- thus last digits is 1,3,7,9. ie., 1,3,-1,-3
      rw [mul_comm (n/10) 10] at h1
      rcases h2 with m1 | m3 | m5 | m7 | m9
      · use (n/10); left; left; rw [← m1, ← h1]
      · use (n/10); rw [← m3, ← h1]
        simp only [true_or, or_true]
      · simp only [m5, ne_eq, not_true_eq_false] at h3
      · use (n/10 + 1); right; right
        rw [Nat.mul_add]; nth_rw 1 [h1, m7]
        simp only [mul_one, Nat.reduceSubDiff]
      · use (n/10 + 1); left; right
        nth_rw 1 [h1, m9]; rw [Nat.mul_add]
        simp only [mul_one, Nat.add_one_sub_one]
    -- but if n = 10k +- m, then must be the case n=m, given digits are all odd.
    have neqm{m k:ℕ}(hn: n = 10*k + m ∨ n = 10*k - m)(hm: m = 1 ∨ m = 3): n = m := by
      -- if n^2 = 20 x something + m^2, then must be the case something = 0
      -- otherwise there are even digits.
      have{kk: ℕ}(hh: n^2 = 20*kk + m^2): kk=0 := by
        have h1: (n^2 / 10) = 2*kk := by
          rcases hm with (rfl | rfl)
          all_goals
            simp [hh]
            omega
        -- so second last digits of n^2 is 2,4,6,8,10. even. contradiction.
        have h2: ¬ Odd (n^2/10 % 10) := by
          refine Nat.not_odd_iff_even.mpr ?_
          rw [h1]
          refine Even.mod_even ?_ (by exact Nat.even_iff.mpr rfl)
          exact even_two_mul kk
        absurd h2
        apply h _ (second_last ?_)
        omega
      -- expand n^2, coefficients of 20 must = 0, otherwise have even digits.
      -- and therefore we solve n = m.
      have eq_of{kk:ℕ}(hkk: kk = 0)(heq: n^2 = 20*kk + m^2): n = m := by
        simp [hkk] at heq
        exact heq
      rcases hn with hn1 | hn2
      · replace hn1: n^2 = 20 * (k*(5*k+m)) + m^2 := by
          rw [hn1]; ring
        apply eq_of (this hn1) hn1
      · -- since we work on natural numbers with tsub, given n = 10k-m
        -- we have to prove some order relation while doing tsub-simplification.
        -- following are some calculations.
        have hmk: m < 10*k := by
          by_contra!
          replace hn2: n = 0 := by
            rw [hn2]; apply Nat.sub_eq_zero_of_le this
          simp [hn2] at oddn
        have hk: 0 < k := by omega
        replace hn2: n^2 = 20* (k*(5*k-m)) + m^2 := by
          rw [hn2]
          simp [Nat.pow_two, Nat.mul_sub, Nat.sub_mul]
          ring_nf
          replace hmk: m^2 ≤ k*m*10 := by
            apply le_of_lt
            rw [pow_two, mul_comm k m, mul_assoc, mul_comm k 10]
            refine Nat.mul_lt_mul_of_pos_left hmk ?_
            rcases hm with hm | hm
            all_goals simp [hm]
          rw [← Nat.Simproc.add_sub_le _ hmk, add_comm _ (m^2)]
          have: k*m*10 ≤ k^2 * 100 - k*m*10 := by
            rw [pow_two, mul_assoc k _ _, mul_assoc k _ _, ← Nat.mul_sub]
            apply Nat.mul_le_mul_left k ?_
            omega
          rw [Nat.add_sub_assoc this]
          simp only [add_right_inj]
          omega
        apply eq_of (this hn2) hn2
    -- done.
    rcases n_of_km with ⟨k, hkm⟩
    rcases hkm with k1 | k3
    · left; apply neqm k1 (by trivial)
    · right; apply neqm k3 (by trivial)
  · -- obviously, n=1, n=3 have odd digits.
    have: Odd 9 := by exact Nat.odd_iff.mpr rfl
    rintro (rfl | rfl)
    all_goals simp [this]