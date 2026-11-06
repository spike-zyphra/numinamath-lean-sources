import Mathlib

/- Find all the functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ such that  $$ f(a)^{2}+f(b)^{2}+f(c)^{2}=2 f(a) f(b)+2 f(b) f(c)+2 f(c) f(a) $$  for all integers $a, b, c$ satisfying $a+b+c=0$. -/
theorem algebra_24138 (f : ℤ → ℤ) :
    (∀ a b c, a + b + c = 0 → f a ^ 2 + f b ^ 2 + f c ^ 2 = 2 * f a * f b + 2 * f b * f c + 2 * f c * f a) ↔ ((∀ x, f x = 0) ∨ (∃ k, k ≠ 0 ∧ ∀ x : ℤ, f x = if Odd x then k else 0) ∨ (∃ k, k ≠ 0 ∧ ∀ x : ℤ, f x = if Odd x then k else if 4 ∣ x then 0 else 4 * k) ∨ (∃ k, k ≠ 0 ∧ ∀ x : ℤ, f x = k * x ^ 2)) := by
  -- Break the iff into two implications.
  apply Iff.intro <;> intro h
  . -- If the function satisfies the condition, then it is of the four classes of functions.
    -- We have f(0) = 0.
    have h0 : f 0 = 0 := by
      -- Substitute a = b = c = 0.
      specialize h 0 0 0
      ring_nf at h
      simp at h
      exact h
    -- We have f(a) = f(-a) for all a ∈ ℤ.
    have ha (a : ℤ) : f a = f (-a) := by
      -- Substitute b = -a, c = 0.
      specialize h a (-a) 0
      ring_nf at h
      simp [h0] at h
      replace h : (f a - f (-a)) ^ 2 = 0 := by
        linarith only [h]
      rw [sq_eq_zero_iff] at h
      linarith only [h]
    -- We have f(2a) = 0 or f(4a) for all a ∈ ℤ.
    have h2a (a : ℤ) : f (2 * a) = 0 ∨ f (2 * a) = 4 * f a := by
      -- Substitute b = a, c = -2a.
      specialize h a a (-(2 * a))
      rw [<-ha (2 * a)] at h
      ring_nf at h
      simp at h
      replace h : f (2 * a) * (f (2 * a) - 4 * f a) = 0 := by
        ring_nf
        linarith only [h]
      rw [mul_eq_zero] at h
      obtain h | h := h
      . tauto
      . right
        linarith only [h]
    -- We have f periodic if f(r) = 0 for some r ≥ 1.
    have hperiod (r : ℤ) (hr : r ≥ 1) (hfr : f r = 0) : ∀ a : ℤ, f (a + r) = f a := by
      intro a
      -- Substitute b = r, c = -a - r.
      specialize h a r (-a - r)
      rw [ha (-a - r)] at h
      ring_nf at h
      simp [hfr] at h
      replace h : (f (a + r) - f a) ^ 2 = 0 := by
        linarith only [h]
      rw [sq_eq_zero_iff] at h
      linarith only [h]
    by_cases g₀ : f 1 = 0
    . -- If f(1) = 0, f is constantly zero.
      left
      have g₁ (n : ℕ) : f n = 0 ∧ f (-n) = 0 := by
        induction n with
        | zero =>
          norm_cast
        | succ n gn =>
          obtain ⟨gn₁, gn₂⟩ := gn
          refine ⟨?_, ?_⟩
          . rw [show (n + 1 : ℕ) = (n : ℤ) + 1 by norm_cast]
            rw [hperiod]
            exact gn₁
            norm_num
            exact g₀
          . rw [show -(n + 1 : ℕ) = (-n : ℤ) - 1 by norm_cast; exact Int.negSucc_coe' n]
            rw [<-hperiod 1]
            simp [gn₂]
            norm_num
            exact g₀
      intro x
      specialize g₁ x.natAbs
      have g₂ : x = x.natAbs ∨ x = -x.natAbs := by
        rw [<-Int.natAbs_eq_iff] -- Or just use Int.natAbs_eq.
      cases g₂ with
      | inl g₂ =>
        rw [<-g₂] at g₁
        tauto
      | inr g₂ =>
        rw [<-g₂] at g₁
        tauto
    . -- Suppose f(1) ≠ 0.
      right
      rw [<-ne_eq] at g₀
      let k : ℤ := f 1
      rw [show f 1 = k by dsimp [k]] at g₀
      have g₁ : f 2 = 0 ∨ f 2 = 4 * k := by
        specialize h2a 1
        simp [show f 1 = k by dsimp [k]] at h2a
        exact h2a
      cases g₁ with
      | inl g₁ =>
        -- If f(2) = 0, f(x) = f(1) for odd x and 0 for even x.
        left
        use k
        simp [g₀]
        intro x
        by_cases g₃ : Odd x
        . simp [g₃]
          simp [Odd] at g₃
          have g₂ (n : ℕ) : f (2 * n + 1) = k ∧ f (-(2 * n + 1)) = k := by
            induction n with
            | zero =>
              simp [<-ha]
            | succ n gn =>
              obtain ⟨gn₁, gn₂⟩ := gn
              refine ⟨?_, ?_⟩
              . rw [show (2 * (n + 1 : ℕ) + 1 : ℤ) = 2 * (n : ℕ) + 1 + 2 by norm_cast]
                rw [hperiod]
                exact gn₁
                norm_num
                exact g₁
              . rw [show -(2 * (n + 1 : ℕ) + 1 : ℤ) = -(2 * (n : ℕ) + 1) - 2 by norm_cast]
                rw [<-hperiod 2]
                simp only [sub_add_cancel]
                exact gn₂
                norm_num
                exact g₁
          obtain ⟨n, g₃⟩ := g₃
          by_cases g₅ : n ≥ 0
          . specialize g₂ n.natAbs
            have g₄ : n = n.natAbs ∨ n = -n.natAbs := by
              rw [<-Int.natAbs_eq_iff]
            replace g₄ : n = n.natAbs := by
              obtain g₄ | g₄ := g₄
              . exact g₄
              . replace g₅ : n = 0 := by
                  omega
                simp [g₅]
            rw [<-g₄, <-g₃] at g₂
            tauto
          . specialize g₂ ((n + 1).natAbs)
            obtain ⟨_, g₂⟩ := g₂
            have g₆ : n + 1 = (n + 1).natAbs ∨ n + 1 = -(n + 1).natAbs := by
              rw [<-Int.natAbs_eq_iff]
            replace g₆ : n + 1 = -(n + 1).natAbs := by
              obtain g₆ | g₆ := g₆
              . replace g₅ : n + 1 = 0 := by
                  omega
                simp [g₅]
              . exact g₆
            rw [neg_add, mul_comm, <-Int.neg_mul, <-g₆] at g₂
            ring_nf at g₂ g₃
            rw [<-g₃] at g₂
            exact g₂
        . simp [g₃]
          simp [Even] at g₃
          have g₂ (n : ℕ) : f (2 * n) = 0 ∧ f (-(2 * n)) = 0 := by
            induction n with
            | zero =>
              simp [h0]
            | succ n gn =>
              obtain ⟨gn₁, gn₂⟩ := gn
              refine ⟨?_, ?_⟩
              . rw [show (2 * (n + 1 : ℕ) : ℤ) = 2 * (n : ℕ) + 2 by norm_cast]
                rw [hperiod]
                exact gn₁
                norm_num
                exact g₁
              . rw [show -(2 * (n + 1 : ℕ) : ℤ) = -2 * (n : ℕ) - 2 by norm_cast; rw [Int.negSucc_coe', sub_mul, mul_add]; omega]
                rw [<-hperiod 2]
                simp only [sub_add_cancel]
                exact gn₂
                norm_num
                exact g₁
          obtain ⟨n, g₃⟩ := g₃
          rw [<-two_mul] at g₃
          have g₄ : n = n.natAbs ∨ n = -n.natAbs := by
            rw [<-Int.natAbs_eq_iff]
          specialize g₂ n.natAbs
          cases g₄ with
          | inl g₄ =>
            rw [<-g₄, <-g₃] at g₂
            tauto
          | inr g₄ =>
            rw [<-Int.neg_mul, Int.neg_mul_comm, <-g₄, <-g₃] at g₂
            tauto
      | inr g₁ =>
        -- Suppose f(2) = 4k.
        right
        have g₂ : f 4 = 0 ∨ f 4 = 16 * k := by
          specialize h2a 2
          simp [g₁] at h2a
          omega
        cases g₂ with
        | inl g₂ =>
          -- If f(4) = 0, we get the third possible solution.
          left
          use k
          simp [g₀]
          intro x
          by_cases g₃ : Odd x
          . simp [g₃]
            simp [Odd] at g₃
            have g₂ (n : ℕ) : f (4 * n + 1) = k ∧ f (4 * n + 3) = k ∧ f (4 * -n + 1) = k ∧ f (4 * -n + 3) = k := by
              induction n with
              | zero =>
                simp [<-ha]
                rw [show 3 = -1 + 4 by norm_num, hperiod, <-ha]
                norm_num
                exact g₂
              | succ n gn =>
                obtain ⟨gn₁, gn₂, gn₃, gn₄⟩ := gn
                refine ⟨?_, ?_, ?_, ?_⟩
                . rw [show (4 * (n + 1 : ℕ) + 1 : ℤ) = 4 * (n : ℕ) + 1 + 4 by norm_cast]
                  rw [hperiod]
                  exact gn₁
                  norm_num
                  exact g₂
                . rw [show (4 * (n + 1: ℕ) + 3 : ℤ) = 4 * (n : ℕ) + 3 + 4 by norm_cast]
                  rw [hperiod]
                  exact gn₂
                  norm_num
                  exact g₂
                . rw [show (4 * -(n + 1 : ℕ) + 1 : ℤ) = 4 * -(n : ℕ) + 1 - 4 by norm_cast; rw [Int.negSucc_coe', mul_sub]; ring_nf]
                  rw [<-hperiod 4]
                  simp only [sub_add_cancel]
                  exact gn₃
                  norm_num
                  exact g₂
                . rw [show (4 * -(n + 1 : ℕ) + 3 : ℤ) = 4 * -(n : ℕ) + 3 - 4 by norm_cast; rw [Int.negSucc_coe', mul_sub]; ring_nf]
                  rw [<-hperiod 4]
                  simp only [sub_add_cancel]
                  exact gn₄
                  norm_num
                  exact g₂
            obtain ⟨n, g₃⟩ := g₃
            by_cases g₄ : Odd n
            . simp [Odd] at g₄
              obtain ⟨m, g₄⟩ := g₄
              rw [g₄, show 2 * (2 * m + 1) + 1 = 4 * m + 3 by ring_nf] at g₃
              have g₅ : m = m.natAbs ∨ m = -m.natAbs := by
                rw [<-Int.natAbs_eq_iff]
              specialize g₂ m.natAbs
              cases g₅ with
              | inl g₅ =>
                rw [<-g₅, <-g₃] at g₂
                tauto
              | inr g₅ =>
                rw [<-g₅, <-g₃] at g₂
                tauto
            . simp [Even] at g₄
              obtain ⟨m, g₄⟩ := g₄
              rw [<-two_mul] at g₄
              rw [g₄, <-mul_assoc] at g₃
              norm_num at g₃
              have g₅ : m = m.natAbs ∨ m = -m.natAbs := by
                rw [<-Int.natAbs_eq_iff]
              specialize g₂ m.natAbs
              cases g₅ with
              | inl g₅ =>
                rw [<-g₅, <-g₃] at g₂
                tauto
              | inr g₅ =>
                rw [<-g₅, <-g₃] at g₂
                tauto
          . simp [g₃]
            simp at g₃
            by_cases g₄ : 4 ∣ x
            . simp [g₄]
              rw [dvd_iff_exists_eq_mul_right] at g₄
              obtain ⟨n, g₄⟩ := g₄
              have g₅ (n : ℕ) : f (4 * n) = 0 ∧ f (4 * -n) = 0 := by
                induction n with
                | zero =>
                  simp [h0]
                | succ n gn =>
                  obtain ⟨gn₁, gn₂⟩ := gn
                  refine ⟨?_, ?_⟩
                  . rw [show (4 * (n + 1 : ℕ) : ℤ) = 4 * n + 4 by norm_cast]
                    rw [hperiod]
                    exact gn₁
                    norm_num
                    exact g₂
                  . rw [show (4 * -(n + 1 : ℕ) : ℤ) = 4 * -n - 4 by norm_cast; rw [Int.negSucc_coe', mul_sub]; norm_num]
                    rw [<-hperiod 4]
                    simp only [sub_add_cancel]
                    exact gn₂
                    norm_num
                    exact g₂
              have g₆ : n = n.natAbs ∨ n = -n.natAbs := by
                rw [<-Int.natAbs_eq_iff]
              specialize g₅ n.natAbs
              cases g₆ with
              | inl g₆ =>
                rw [<-g₆, <-g₄] at g₅
                tauto
              | inr g₆ =>
                rw [<-g₆, <-g₄] at g₅
                tauto
            . simp [g₄]
              simp [Even] at g₃
              obtain ⟨n, g₃⟩ := g₃
              have g₅ : Odd n := by
                by_contra! g₅
                simp [Even] at g₅
                obtain ⟨m, g₅⟩ := g₅
                rw [g₅, show m + m + (m + m) = 4 * m by ring_nf] at g₃
                rw [g₃] at g₄
                absurd g₄
                norm_num
              simp [Odd] at g₅
              obtain ⟨m, g₅⟩ := g₅
              rw [g₅, show 2 * m + 1 + (2 * m + 1) = 4 * m + 2 by ring_nf] at g₃
              have g₆ (n : ℕ) : f (4 * n + 2) = 4 * k ∧ f (4 * -n + 2) = 4 * k := by
                induction n with
                | zero =>
                  simp [g₁]
                | succ n gn =>
                  obtain ⟨gn₁, gn₂⟩ := gn
                  refine ⟨?_, ?_⟩
                  . rw [show (4 * (n + 1 : ℕ) + 2 : ℤ) = 4 * n + 2 + 4 by norm_cast]
                    rw [hperiod]
                    exact gn₁
                    norm_num
                    exact g₂
                  . rw [show (4 * -(n + 1 : ℕ) + 2 : ℤ) = 4 * -n + 2 - 4 by norm_cast; rw [Int.negSucc_coe', mul_sub]; ring_nf]
                    rw [<-hperiod 4]
                    simp only [sub_add_cancel]
                    exact gn₂
                    norm_num
                    exact g₂
              have g₇ : m = m.natAbs ∨ m = -m.natAbs := by
                rw [<-Int.natAbs_eq_iff]
              specialize g₆ m.natAbs
              cases g₇ with
              | inl g₇ =>
                rw [<-g₇, <-g₃] at g₆
                tauto
              | inr g₇ =>
                rw [<-g₇, <-g₃] at g₆
                tauto
        | inr g₂ =>
          -- Suppose f(4) = 16k. We shall prove that f(x) = kx².
          right
          use k
          simp [g₀]
          intro x
          -- We shall show that f(3) = 9k by substituting a = 1, b = 2, c = -3; a = 1, b = 3, c = -4.
          have h₁ := h
          have h₂ := h
          specialize h₁ 1 2 (-3)
          simp [show f 1 = k by dsimp [k], g₁, <-ha] at h₁
          replace h₁ : (f 3 - k) * (f 3 - 9 * k) = 0 := by
            linarith only [h₁]
          rw [mul_eq_zero] at h₁
          specialize h₂ 1 3 (-4)
          simp [show f 1 = k by dsimp [k], g₂, <-ha] at h₂
          replace h₂ : (f 3 - 9 * k) * (f 3 - 25 * k) = 0 := by
            linarith only [h₂]
          rw [mul_eq_zero] at h₂
          have g₃ : f 3 = 9 * k := by
            cases h₁ with
            | inl h₁ =>
              cases h₂ with
              | inl h₂ =>
                linarith only [h₂]
              | inr h₂ =>
                linarith only [g₀, h₁, h₂]
            | inr h₁ =>
              linarith only [h₁]
          clear h₁ h₂
          have g₄_base : ∀ x : ℤ, 0 ≤ x ∧ x ≤ 4 → f x = k * x ^ 2 := by
            intro x ⟨g₄, g₅⟩
            interval_cases x
            . simp [h0]
            . simp [show f 1 = k by dsimp [k]]
            . simp [g₁, mul_comm]
            . simp [g₃, mul_comm]
            . simp [g₂, mul_comm]
          have g₄ (n : ℕ) : ∀ x : ℤ, 0 ≤ x ∧ x ≤ n → f x = k * x ^ 2 := by
            induction n with
            | zero =>
              intro x g₄
              apply g₄_base
              omega
            | succ n gn =>
              by_cases nrange : n ≤ 3
              . interval_cases n
                all_goals
                  intro x nrange
                  apply g₄_base
                  omega
              . replace nrange : n ≥ 4 := by
                  omega
                have h₁ := h
                have h₂ := h
                let x : ℤ := n
                have g₅ : f x = k * x ^ 2 := by
                  apply gn
                  simp [x]
                have g₆ : f (x - 1) = k * (x - 1) ^ 2 := by
                  apply gn
                  simp [x]
                  omega
                -- Substitute a = x, b = 1, c = -x - 1.
                specialize h₁ x 1 (-x - 1)
                simp [show f 1 = k by dsimp [k], g₅] at h₁
                rw [show -x - 1 = -(x + 1) by ring_nf, <-ha] at h₁
                replace h₁ : (f (x + 1) - k * (x + 1) ^ 2) * (f (x + 1) - k * (x - 1) ^ 2) = 0 := by
                  linarith only [h₁]
                rw [mul_eq_zero] at h₁
                -- Substitute a = x - 1, b = 2, c = -x - 1.
                specialize h₂ (x - 1) 2 (-x - 1)
                simp [show x - 1 + 2 + (-x - 1) = 0 by ring_nf, g₁, g₅, g₆] at h₂
                rw [show -x - 1 = -(x + 1) by ring_nf, <-ha] at h₂
                replace h₂ : (f (x + 1) - k * (x + 1) ^ 2) * (f (x + 1) - k * (x - 3) ^ 2) = 0 := by
                  linarith only [h₂]
                rw [mul_eq_zero] at h₂
                have g₇ : f (x + 1) = k * (x + 1) ^ 2 := by
                  cases h₁ with
                  | inl h₁ =>
                    linarith only [h₁]
                  | inr h₁ =>
                    cases h₂ with
                    | inl h₂ =>
                      linarith only [h₂]
                    | inr h₂ =>
                      have weq : k * (x - 1) ^ 2 = k * (x - 3) ^ 2 := by
                        linarith only [h₁, h₂]
                      nth_rewrite 1 [mul_comm] at weq
                      nth_rewrite 2 [mul_comm] at weq
                      apply Int.eq_of_mul_eq_mul_right at weq
                      apply eq_or_eq_neg_of_sq_eq_sq at weq
                      obtain weq | weq := weq
                      . omega
                      . have weq' : x ≥ 4 := by
                          dsimp [x]
                          norm_cast
                        omega
                      exact g₀
                intro y g₈
                by_cases g₉ : y ≤ n
                . apply gn
                  tauto
                . replace g₉ : y = n + 1 := by
                    omega
                  simp [g₉, show n = x by dsimp [x]]
                  exact g₇
          have g₅ : x = x.natAbs ∨ x = -x.natAbs := by
            rw [<-Int.natAbs_eq_iff]
          cases g₅ with
          | inl g₅ =>
            apply g₄ x.natAbs
            refine ⟨?_, ?_⟩
            . rw [g₅]
              simp
            . rw [<-g₅]
          | inr g₅ =>
            rw [ha, g₅, neg_neg, neg_sq]
            apply g₄ x.natAbs
            simp
  . -- The four classes of functions do satisfy the condition.
    obtain h | ⟨k, ⟨h₁, h⟩⟩ | ⟨k, ⟨h₁, h⟩⟩ | ⟨k, ⟨h₁, h⟩⟩ := h
    . intro a b c hsum
      repeat rewrite [h]
      simp
    . intro a b c hsum
      by_cases aOdd : Odd a
      . by_cases bOdd : Odd b
        . have cEven : ¬Odd c := by
            by_contra! cOdd
            -- a, b and c cannot all be odd, otherwise contradicting a + b + c = 0.
            simp [Odd] at aOdd bOdd cOdd
            obtain ⟨a', ha⟩ := aOdd
            obtain ⟨b', hb⟩ := bOdd
            obtain ⟨c', hc⟩ := cOdd
            rw [ha, hb, hc] at hsum
            omega
          rw [show f a = k by simp [aOdd, h a], show f b = k by simp [bOdd, h b], show f c = 0 by simp [cEven, h c]]
          ring_nf
        . have bEven := bOdd
          clear bOdd
          have cOdd : Odd c := by
            by_contra! cEven
            simp [Odd] at aOdd
            simp [Even] at bEven cEven
            obtain ⟨a', ha⟩ := aOdd
            obtain ⟨b', hb⟩ := bEven
            obtain ⟨c', hc⟩ := cEven
            rw [ha, hb, hc] at hsum
            omega
          rw [show f a = k by simp [aOdd, h a], show f b = 0 by simp [bEven, h b], show f c = k by simp [cOdd, h c]]
          ring_nf
      . have aEven := aOdd
        clear aOdd
        by_cases bOdd : Odd b
        . have cOdd : Odd c := by
            by_contra! cEven
            simp [Odd] at bOdd
            simp [Even] at aEven cEven
            obtain ⟨a', ha⟩ := aEven
            obtain ⟨b', hb⟩ := bOdd
            obtain ⟨c', hc⟩ := cEven
            rw [ha, hb, hc] at hsum
            omega
          rw [show f a = 0 by simp [aEven, h a], show f b = k by simp [bOdd, h b], show f c = k by simp [cOdd, h c]]
          ring_nf
        . have bEven := bOdd
          clear bOdd
          have cEven : ¬Odd c := by
            by_contra! cOdd
            simp [Odd] at cOdd
            simp [Even] at aEven bEven
            obtain ⟨a', ha⟩ := aEven
            obtain ⟨b', hb⟩ := bEven
            obtain ⟨c', hc⟩ := cOdd
            rw [ha, hb, hc] at hsum
            omega
          rw [show f a = 0 by simp [aEven, h a], show f b = 0 by simp [bEven, h b], show f c = 0 by simp [cEven, h c]]
          ring_nf
    . intro a b c hsum
      by_cases aOdd : Odd a
      . by_cases bOdd : Odd b
        . have cEven : ¬Odd c := by
            by_contra! cOdd
            -- a, b and c cannot all be odd, otherwise contradicting a + b + c = 0.
            simp [Odd] at aOdd bOdd cOdd
            obtain ⟨a', ha⟩ := aOdd
            obtain ⟨b', hb⟩ := bOdd
            obtain ⟨c', hc⟩ := cOdd
            rw [ha, hb, hc] at hsum
            omega
          by_cases cdvd4 : 4 ∣ c
          . rw [show f a = k by simp [aOdd, h a], show f b = k by simp [bOdd, h b], show f c = 0 by simp [cEven, cdvd4, h c]]
            ring_nf
          . rw [show f a = k by simp [aOdd, h a], show f b = k by simp [bOdd, h b], show f c = 4 * k by simp [cEven, cdvd4, h c]]
            ring_nf
        . have bEven := bOdd
          clear bOdd
          have cOdd : Odd c := by
            by_contra! cEven
            simp [Odd] at aOdd
            simp [Even] at bEven cEven
            obtain ⟨a', ha⟩ := aOdd
            obtain ⟨b', hb⟩ := bEven
            obtain ⟨c', hc⟩ := cEven
            rw [ha, hb, hc] at hsum
            omega
          by_cases bdvd4 : 4 ∣ b
          . rw [show f a = k by simp [aOdd, h a], show f b = 0 by simp [bEven, bdvd4, h b], show f c = k by simp [cOdd, h c]]
            ring_nf
          . rw [show f a = k by simp [aOdd, h a], show f b = 4 * k by simp [bEven, bdvd4, h b], show f c = k by simp [cOdd, h c]]
            ring_nf
      . have aEven := aOdd
        clear aOdd
        by_cases bOdd : Odd b
        . have cOdd : Odd c := by
            by_contra! cEven
            simp [Odd] at bOdd
            simp [Even] at aEven cEven
            obtain ⟨a', ha⟩ := aEven
            obtain ⟨b', hb⟩ := bOdd
            obtain ⟨c', hc⟩ := cEven
            rw [ha, hb, hc] at hsum
            omega
          by_cases advd4 : 4 ∣ a
          . rw [show f a = 0 by simp [aEven, advd4, h a], show f b = k by simp [bOdd, h b], show f c = k by simp [cOdd, h c]]
            ring_nf
          . rw [show f a = 4 * k by simp [aEven, advd4, h a], show f b = k by simp [bOdd, h b], show f c = k by simp [cOdd, h c]]
            ring_nf
        . have bEven := bOdd
          clear bOdd
          have cEven : ¬Odd c := by
            by_contra! cOdd
            simp [Odd] at cOdd
            simp [Even] at aEven bEven
            obtain ⟨a', ha⟩ := aEven
            obtain ⟨b', hb⟩ := bEven
            obtain ⟨c', hc⟩ := cOdd
            rw [ha, hb, hc] at hsum
            omega
          by_cases advd4 : 4 ∣ a
          . by_cases bdvd4 : 4 ∣ b
            . have cdvd4 : 4 ∣ c := by
                rw [show c = -a - b by linarith only [hsum]]
                omega
              rw [show f a = 0 by simp [aEven, advd4, h a], show f b = 0 by simp [bEven, bdvd4, h b], show f c = 0 by simp [cEven, cdvd4, h c]]
              ring_nf
            . have cdvd4 : ¬4 ∣ c := by
                by_contra! cdvd4
                rw [show b = -a - c by linarith only [hsum]] at bdvd4
                omega
              rw [show f a = 0 by simp [aEven, advd4, h a], show f b = 4 * k by simp [bEven, bdvd4, h b], show f c = 4 * k by simp [cEven, cdvd4, h c]]
              ring_nf
          . by_cases bdvd4 : 4 ∣ b
            . have cdvd4 : ¬4 ∣ c := by
                by_contra! cdvd4
                rw [show a = -b - c by linarith only [hsum]] at advd4
                omega
              rw [show f a = 4 * k by simp [aEven, advd4, h a], show f b = 0 by simp [bEven, bdvd4, h b], show f c = 4 * k by simp [cEven, cdvd4, h c]]
              ring_nf
            . have cdvd4 : 4 ∣ c := by
                simp [Even] at aEven bEven cEven
                obtain ⟨a', ha⟩ := aEven
                obtain ⟨b', hb⟩ := bEven
                obtain ⟨c', hc⟩ := cEven
                rw [ha, hb, hc] at hsum
                omega
              rw [show f a = 4 * k by simp [aEven, advd4, h a], show f b = 4 * k by simp [bEven, bdvd4, h b], show f c = 0 by simp [cEven, cdvd4, h c]]
              ring_nf
    . intro a b c hsum
      repeat rewrite [h]
      rw [show c = -b - a by linarith only [hsum]]
      ring_nf
