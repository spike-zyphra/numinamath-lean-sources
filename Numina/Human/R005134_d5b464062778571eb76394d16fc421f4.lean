import Mathlib


/- Vind alle functies $f: \mathbb{Z}_{>0} \rightarrow \mathbb{Z}_{>0}$ zodat $f(1)=2$ en zodat voor alle $m, n \in \mathbb{Z}_{>0}$ geldt dat $\min (2 m+2 n, f(m+n)+1)$ deelbaar is door $\max (f(m)+f(n), m+n)$. -/
theorem number_theory_605715 {f: ℕ → ℕ}
  (fpos: ∀ n, 0 < n → 0 < f n)
  (f1eq: f 1 = 2):
  (∀ (m n:ℕ), 0 < m → 0 < n →
    max (f m + f n) (m+n) ∣ min (2*m+2*n) (f (m+n) + 1)) ↔
  ((∀n, 0 < n → f n = n + 1) ∨
    (∀n, 0 < n → f n = 2*n) ) := by

  constructor
  · intro h
    -- we claim fn ≤ 2n
    have fub {n:ℕ} (npos: 0 < n): f n ≤ 2*n := by
      by_contra!
      have hdvd := h n n npos npos
      -- take m=n, max (2fn, 2n) ∣ min (4n, f(2n) + 1)
      have h1: max (f n + f n) (n+n) = f n + f n := by
        refine Nat.max_eq_left ?_
        linarith only [this]
      have h2: min (2*n + 2*n) (f (n+n) + 1) ≤ 2*n + 2*n :=
        Nat.min_le_left _ _
      -- left side ≤ right side ≤ 4n
      have h3: 0 < min (2*n+2*n) (f (n+n) + 1) := by
        refine Nat.lt_min.mpr ?_
        constructor <;> positivity
      have h4 := Nat.le_of_dvd h3 hdvd
      -- contradiction.
      rw [h1] at h4
      replace h4 := h4.trans h2
      linarith only [this, h4]

    -- then f2 = 3 or 4.
    have f2eq: f 2 = 3 ∨ f 2 = 4 := by
      -- take m=n=1 at problem statement
      specialize h 1 1 (by norm_num) (by norm_num)
      norm_num [f1eq] at h
      specialize @fub 2 (by norm_num)
      specialize fpos 2 (by norm_num)
      have f2eq: f 2 = 1 ∨ f 2 = 2 ∨ f 2 = 3 ∨ f 2 = 4 := by omega
      rcases f2eq with f2eq | f2eq | f2eq | f2eq
      any_goals norm_num [f2eq] at h
      all_goals simp [f2eq]

    rcases f2eq with f2eq | f2eq

    · -- f2 = 3 case, we claim fn = n+1
      left
      intro n npos
      induction' n,npos using Nat.le_induction with n npos ih
      · simp [f1eq]
      · -- take m = 1, n=n
        specialize h 1 n (by norm_num) npos
        have h1: max (f 1 + f n) (1 + n) = n + 3 := by
          rw [ih, f1eq, Nat.max_eq_left (by linarith only)]
          ring
        by_cases hhn: n = 1
        · simp [hhn, f2eq]
        -- f (n+1) + 1 < 2n+2, otherwise divide condition does not hold.
        have h2: f (1+n) + 1 < 2*1 + 2*n := by
          by_contra!
          rw [Nat.min_eq_left this, h1] at h
          rcases h with ⟨d, hd⟩
          have dpos: 0 < d := by
            by_contra!
            replace: d = 0 := by omega
            simp [this] at hd
          have dgt: d > 1 := by
            by_contra!
            replace: d = 1 := by omega
            rw [this, mul_one, mul_one] at hd
            replace hd: n = 1 := by omega
            simp [hd] at hhn
          have dlt: d < 2 := by
            by_contra!
            replace: (n+3)*d ≥ (n+3)*2 := by
              exact Nat.mul_le_mul_left (n + 3) dgt
            rw [← hd] at this
            linarith only [this]
          omega
        rw [Nat.min_eq_right h2.le, h1] at h
        -- n+3 divide f(n+1) + 1, f(n+1) can only be n+2
        rcases h with ⟨d, hd⟩
        have dpos: 0 < d := by
          have: 0 < f (1+n) + 1 := by positivity
          rw [hd] at this
          exact Nat.pos_of_mul_pos_left this
        have dlt: d < 2 := by
          by_contra!
          have: (n+3)*d ≥ (n+3)*2 := by
            exact Nat.mul_le_mul_left (n + 3) this
          rw [← hd] at this
          linarith only [h2, this]
        have deq: d = 1 := by omega
        rw [deq] at hd
        rw [add_comm n 1]
        omega

    · -- f2 = 4 case, we claim fn = 2n
      right
      intro n npos
      induction' n,npos using Nat.le_induction with n npos ih
      · simp [f1eq]
      · -- take m = 1, n=n
        have hh := h 1 n (by norm_num) npos
        have h1: max (f 1 + f n) (1+n) = 2 * n + 2 := by
          rw [Nat.max_eq_left, f1eq, ih]
          ring
          rw [ih, f1eq]
          linarith only
        -- right side ≤ 2 + 2n
        have h2: min (2*1 + 2*n) (f (1+n) + 1) ≤ 2*1 + 2*n :=
          Nat.min_le_left _ _
        have h3: 0 < min (2*1 + 2*n) (f (1+n) + 1) := by
          refine Nat.lt_min.mpr ?_
          constructor <;> positivity
        have h4 := Nat.le_of_dvd h3 hh
        rw [h1] at h4
        have h5: min (2*1 + 2*n) (f (1+n) + 1) = 2*n + 2 := by
          apply le_antisymm ?_ h4
          simp only [mul_one, add_comm 2 _, inf_le_left]
        replace h5: 2*1 + 2*n ≤ f (1+n) + 1 := by
          nth_rw 4 [← mul_one 2] at h5
          rw [add_comm (2*n) _] at h5
          exact left_eq_inf.mp h5.symm
        -- then f(n+1) = 2n+1 or 2n+2
        replace h5: f (n+1) = 2*n+1 ∨ f (n+1) = 2*(n+1) := by
          specialize @fub (n+1) (by simp)
          clear * - h5 fub
          rw [mul_one, add_comm 1 n] at h5
          omega
        refine h5.resolve_left ?_
        rintro h6
        -- if f(n+1) = 2n+1, take m = 1, n = n+1, and we can find contradiction.
        have hhh :=  h 1 (n+1) (by norm_num) (by simp)
        have hh1: max (f 1 + f (n+1)) (1 + (n+1)) = 2*n+3 := by
          rw [h6, f1eq, Nat.max_eq_left]
          ring
          linarith only
        -- 2n+3 not divide 2n+3+1
        have not_dvd: ¬ 2*n+3 ∣ 2*n+3+1 := by
          rintro ⟨d,hd⟩
          have dpos: 0 < d := by
            have: 0 < 2*n+3+1 := by positivity
            rw [hd] at this
            exact Nat.pos_of_mul_pos_left this
          have dlt: d < 2 := by
            by_contra!
            have: (2*n+3)*d ≥ (2*n+3) * 2 := by
              exact Nat.mul_le_mul_left (2 * n + 3) this
            rw [← hd] at this
            linarith only [this]
          have deq: d = 1 := by omega
          simp [deq] at hd
        -- must be the case f (1 + (n+1)) + 1 < 2 + 2(n+1)
        have hh2: f (1 + (n+1)) + 1 < 2*1 + 2*(n+1) := by
          by_contra!
          rw [Nat.min_eq_left this, hh1] at hhh
          rw [show 2*1 + 2*(n+1) = 2*n+3 + 1 by ring] at hhh
          -- but 2n+3 does not divide 2n+3+1
          apply not_dvd hhh
        rw [Nat.min_eq_right hh2.le, hh1] at hhh
        -- 2n+3 divide f (n+2) + 1, we solve f(n+2) = 2n+2
        have hh3: f (n+2) = 2*n+2 := by
          rw [show 1 + (n+1) = n+2 by ring] at hhh hh2
          replace hh2: f (n+2) ≤ 2*n + 3 := by omega
          have hh3: f (n+2) ≠ 2*n+3 := by
            rintro hh3
            rw [hh3] at hhh
            apply not_dvd hhh
          replace hh2 := lt_of_le_of_ne hh2 hh3
          replace hh2: f (n+2) ≤ 2*n+2 := Nat.le_of_lt_succ hh2
          refine le_antisymm hh2 ?_
          replace hhh := Nat.le_of_dvd (by positivity) hhh
          linarith only [hhh]
        -- then we take m=2, n=n
        specialize h 2 n (by norm_num) npos
        have hh4: max (f 2 + f n) (2 + n) = 2*n + 4 := by
          rw [f2eq, ih, Nat.max_eq_left]
          ring
          linarith only
        have hh5: min (2*2 + 2*n) (f (2+n) + 1) = 2*n + 3 := by
          rw [add_comm 2 n, hh3, Nat.min_eq_right]
          linarith only
        rw [hh4, hh5] at h
        -- but cannot be the case 2n+4 divide 2n+3, contradiction
        replace h := Nat.le_of_dvd (by positivity) h
        linarith only [h]

  · -- verification
    rintro (h | h)
    all_goals
      intro m n mpos npos
      rw [h m mpos, h n npos, h (m+n) (by positivity),
      Nat.max_eq_left (by linarith only [mpos, npos])]
    · rw [Nat.min_eq_right (by linarith only [mpos, npos])]
      use 1
      ring
    · rw [Nat.min_eq_left (by linarith only)]