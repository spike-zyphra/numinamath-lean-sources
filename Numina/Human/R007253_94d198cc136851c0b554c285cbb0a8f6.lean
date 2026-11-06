import Mathlib

/- Find the smallest positive integer $k$ such that, for every positive integer $n$,
 $6n+k$ is relatively prime to each of $6n+3$, $6n+2$, and $6n+1$. -/
theorem number_theory_23498:
    IsLeast {k:ℕ | 0 < k ∧ ∀ n, 0 < n → Nat.Coprime (6 * n + k) (6 * n + 3) ∧
    Nat.Coprime (6 * n + k) (6 * n + 2) ∧ Nat.Coprime (6 * n + k) (6 * n + 1)} 5 := by
  -- to argue 6n+k coprime with 6n+1,2,3, we consider their gcd
  have h1(k m n:ℕ)(hkm: k ≥ m): Nat.gcd (6*n+k) (6*n+m) = Nat.gcd (6*n+k) (k-m) := by
    have hh1: 6*n+m ≤ 6*n+k := by linarith [hkm]
    have hh2: 6*n+k - (6*n+m) = k-m := by omega
    rw [← Nat.gcd_self_sub_right hh1, hh2]
  rw [IsLeast, lowerBounds]; simp; constructor
  · -- verify 6n+5 is coprime with 6n+1, 6n+2, 6n+3.
    intro n npos
    have cop53: (6*n+5).Coprime (6*n+3) := by
      have: (6*n+5).gcd (6*n+3) = 1 := by
        rw [h1 5 3 n (by norm_num)]; simp
        -- the gcd is gcd of 6n+5 and 5-3=2. but 6n+5 is odd, so gcd must be 1.
        have hh1: Odd 5 := by
          exact Nat.odd_iff.mpr rfl
        have hh2: Even (6*n) := by
          have: Even 6 := Nat.even_iff.mpr rfl
          exact Even.mul_right this n
        exact Even.add_odd hh2 hh1
      exact this
    have cop52: (6*n+5).Coprime (6*n+2) := by
      have: (6*n+5).gcd (6*n+2) = 1 := by
        rw [h1 5 2 n (by norm_num)]; simp
        -- for gcd of 6n+5 and 3, 3 ∣ 6n, but 3 coprime with 5, so gcd is 1
        have hh3: (6*n+5).gcd 3 = Nat.gcd 5 3 := by
          have: 6*n = 3*(2*n) := by ring
          rw [this]
          exact Nat.gcd_mul_left_add_left 5 3 (2 * n)
        rw [hh3]
        norm_num
      exact this
    have cop51: (6*n+5).Coprime (6*n+1) := by
      have: (6*n+5).gcd (6*n+1) = 1 := by
        rw [h1 5 1 n (by norm_num)]; simp
        have hh1: (6*n+5).gcd 4 = (6*n+1).gcd 4 := by
          have: 6*n+1 = 6*n+5 - 4 := by simp
          rw [this]
          apply Eq.symm (Nat.gcd_sub_self_left (by linarith))
        rw [hh1]
        -- factors of 4 are 1,2,4. either is 1 or divided by 2.
        have hh2(m:ℕ): m.gcd 4 = 1 ∨ 2 ∣ m := by
          have tt1: m.gcd 4 ≤ 4 := Nat.gcd_le_right 4 (by norm_num)
          have tt2: m.gcd 4 ∣ 4 := Nat.gcd_dvd_right m 4
          have tt3: m.gcd 4 ∣ m := Nat.gcd_dvd_left m 4
          interval_cases m.gcd 4
          all_goals simp at *
          · exact tt3
          · norm_num at tt2
          · apply Nat.dvd_trans (by norm_num) tt3
        rcases (hh2 (6*n+1)) with hl | hr
        · exact hl
        · -- it's impossible that 2 divide 6n+1
          exfalso; omega
      exact this
    exact ⟨cop53, cop52, cop51⟩
  · intro k kpos hcop
    -- we show 5 is the minimum by proving 1,2,3,4 all fails to satisfy coprime condition
    by_contra! hk
    obtain ⟨cop1, cop2, cop3⟩ := hcop 1 (by norm_num)
    interval_cases k
    <;> simp at *
    norm_num at cop2