import Mathlib

open Nat


/- Determine the maximum value of $m^{2}+n^{2}$ where $m$ and $n$ are integers satisfying  $$ m, n \in\{1,2, \ldots, 100\} \quad \text { and } \quad\left(n^{2}-m n-m^{2}\right)^{2}=1 $$ -/
theorem imo_23769
    (rg : Finset ℤ)
    (h_defrg : rg = Finset.Icc 1 100)
    (s : Set ℤ)
    (h_defs : s = {v : ℤ | ∃ m ∈ rg, ∃ n ∈ rg, (n ^ 2 - m * n - m ^ 2) ^ 2 = 1 ∧ m ^ 2 + n ^ 2 = v})
    : IsGreatest s (55 ^ 2 + 89 ^ 2) := by


  -- lemma, if forall t, a (t + 1) < a t, then there exists one t, a t ≤ 0.
  have l_exist_nonpos (a : ℕ → ℤ) (h : ∀ t, a (t + 1) < a t) : ∃ t, a t ≤ 0 := by
    have t0 : ∀ t, a (t + 1) ≤ a t - 1 := by exact fun t => Int.le_sub_one_of_lt (h t)
    have t1 : ∀ t, a t ≤ a 0 - t := by
      intro t
      induction t with
      | zero => exact Int.le.intro 0 rfl
      | succ t ih =>
        rw [Nat.cast_add, Nat.cast_one, ← sub_sub]
        specialize t0 (t)
        linarith only [t0, ih]
    rcases Int.le_or_lt (a 0) 0 with ha0 | ha0
    . use 0
    use (a 0).toNat
    trans a 0 - (a 0).toNat
    . exact t1 (a 0).toNat
    . rw [Int.toNat_of_nonneg (Int.le_of_lt ha0)]
      exact Int.sub_left_le_of_le_add (t1 0)

  -- lemma, if there exists one t such that a t ≤ 0, then there exists an t' such that a t ≤ 0 and forall 0 ≤ i ≤ t, a i > 0.
  have l_exist_min_nonpos (a : ℕ → ℤ) (h2 : ∃ t, a t ≤ 0) :
      ∃ t, a t ≤ 0 ∧ ∀ i < t, 0 < a i:= by
    set s := {x | a x ≤ 0}
    have h_nonempty : s.Nonempty := h2
    let t' := wellFounded_lt.min s h_nonempty
    have : a t' ≤ 0 := by
      have : t' ∈ s := by apply WellFounded.min_mem
      convert this
    have : ∀ i < t', 0 < a i := by
      intro i hi
      by_contra! h_contra
      have h_in : i ∈ s := by simp [s, h_contra]
      have : ¬ i < t' := WellFounded.not_lt_min wellFounded_lt s h_nonempty h_in
      contradiction
    use t'

  -- define the prop that a pair x y is a solution
  let valid_prop : ℤ → ℤ → Prop := fun x y => x ∈ rg ∧ y ∈ rg ∧ (y ^ 2 - x * y - x ^ 2) ^ 2 = 1

  -- For m = 1, n can be either 1 or 2.
  have t1 : ∀ n, valid_prop 1 n → n = 1 ∨ n = 2 := by
    simp_rw [valid_prop, and_imp, h_defrg, Finset.mem_Icc, le_refl, one_le_ofNat, and_self, one_mul, one_pow, sq_eq_one_iff, sub_eq_neg_self, true_implies]
    intro n hn heq
    rcases heq with h | h
    . right
      have : (n - 2) * (n + 1) = 0 := by ring_nf; linarith only [h]
      rcases Int.mul_eq_zero.mp this <;> linarith
    . left
      have : n ^ 2 = n := Int.eq_of_sub_eq_zero h
      rcases eq_zero_or_one_of_sq_eq_self this <;> linarith

  -- If $m>1$, then $n(n-m)=m^{2} \pm 1>0$; hence $n-m>0$.
  have t2 : ∀ m > 1, ∀ n, valid_prop m n → m < n := by
    simp_rw [valid_prop, gt_iff_lt, and_imp, h_defrg, Finset.mem_Icc, sq_eq_one_iff]
    intro m h_mgt n _ ⟨h_nge, _⟩ heq
    have : n * (n - m) > 0 := by
      have : 1 < m ^ 2 := one_lt_pow h_mgt two_ne_zero
      rcases heq with h | h <;> linarith only [this, h]
    exact Int.lt_of_sub_pos ((pos_iff_pos_of_mul_pos this).mp h_nge)

  -- Set $p=n-m$. Since $m^{2}-m p-p^{2}=m^{2}-p(m+p)=$ $-\left(n^{2}-n m-m^{2}\right)$, we see that $(m, n)$ is a solution of the equation if and only if $(p, m)$ is a solution too.
  have t3 : ∀ m > 1, ∀ n, valid_prop m n → valid_prop (n - m) m := by
    intro m h_mgt n h_valid
    have h_ngtm : n > m := t2 m h_mgt n h_valid
    dsimp only [valid_prop] at h_valid
    obtain ⟨hm, hn, heq⟩ := h_valid
    dsimp only [valid_prop]
    have r_nsubm : n - m ∈ rg := by
      rw [h_defrg, Finset.mem_Icc] at hm hn
      rw [h_defrg, Finset.mem_Icc, tsub_le_iff_right]
      omega
    have r_eq : (m ^ 2 - (n - m) * m - (n - m) ^ 2) ^ 2 = 1 := by
      rw [← heq]
      ring_nf
    exact ⟨r_nsubm, hm, r_eq⟩

  -- Therefore, all the solutions of the equation are given as two consecutive members of the Fibonacci sequence
  have t4 : ∀ m n, valid_prop m n → ∃ k, m = fib k ∧ n = fib (k + 1) := by
    intro m n h_valid

    rcases eq_or_ne m 1 with h_meqone | h_mneone

    -- If m = 1, then n = 1 or n = 2, we can set k = 1 or k = 2.
    . rw [h_meqone] at h_valid
      rcases t1 n h_valid with h_neqone | h_neqtwo
      . use 1
        norm_num [h_meqone, h_neqone]
      . use 2
        norm_num [h_meqone, h_neqtwo]

    -- If m ≠ 1, we have m > 1 as m ∈ rg
    have h_mgtone : m > 1 := by
      obtain ⟨hm, _⟩ := h_valid
      simp [h_defrg] at hm
      omega

    have h_mlen : m < n := t2 m h_mgtone n h_valid

    let a : ℕ → ℤ := fun t => (-1) ^ (t + 1) * fib t
    let b : ℕ → ℤ := fun t => a t * n + a (t + 1) * m

    -- set b 0 = m, b 1 = m - n, b (t + 2) = b t - b (t + 1)
    have h_b : ∀ t, b (t + 2) = b t - b (t + 1) := by
      intro t
      simp only [b, a,
        show fib (t + 2 + 1) = fib (t + 1) + fib (t + 2) by exact fib_add_two,
        show fib (t + 2) = fib t + fib (t + 1) by exact fib_add_two, Nat.cast_add]
      ring_nf

    -- if forall 0 ≤ i ≤ t + 1, b i ∈ rg, then (b (t + 1), b t) is a solution.
    have l_1 : ∀ t, (∀ i ≤ t + 1, b i ∈ rg) → valid_prop (b (t + 1)) (b t) := by
      intro t
      have ⟨hn, hm, _⟩ := h_valid
      induction t with
      | zero =>
        intro
        simp [b, a, hm, hn, show n + -m = n - m by exact rfl]
        exact t3 m h_mgtone n h_valid
      | succ t ih =>
        intro h_inrg
        specialize h_b t
        rw [show t + 1 + 1 = t + 2 by rfl, h_b]

        have r0 : ∀ i ≤ t + 1, b i ∈ rg := by
          intro i hi
          exact h_inrg i (le_add_right_of_le hi)
        replace ih := ih r0

        rcases eq_or_ne (b (t + 1)) 1 with h | h
        -- If b (t + 1) = 1, then b t = 1 or b t = 2 as (b (t + 1), b t) is valid, then we can easily verify
        . rw [h] at ih
          rcases t1 (b t) ih with h' | h'
          . specialize h_inrg (t + 2) (by norm_num)
            simp [h_defrg, h_b, h, h'] at h_inrg
          . simp [h, h', valid_prop, h_defrg]
        -- If b (t + 1) ≠ 1, then b (t + 1) > 1, and by apply t3 (valid_prop m n → valid_prop (n - m) m), we can verify
        . have h_gt1 : 1 < b (t + 1) := by
            have h1 := h_inrg (t + 1)
            simp [h_defrg] at h1
            obtain ⟨h11, h12⟩ := h1
            omega
          exact t3 (b (t + 1)) h_gt1 (b t) ih

    -- we can proof that there must be a consecutive pair (1, 1) in sequence b, and all consecutive pair before (1, 1) are valid solutions.
    have : ∃ t, (b (t + 1) = 1 ∧ b t = 1 ∧ ∀ i ≤ (t + 1), b i ∈ rg) := by

      have h_b0 : b 0 = m := by simp [b, a]
      have h_b1 : b 1 = n - m := by simp [b, a]; ring

      have h_b1pos : 0 < b 1 := by
        rw [h_b1]
        exact Int.sub_pos_of_lt h_mlen

      have : ∃ t, b t ≤ 0 ∧ ∀ i < t, 0 < b i := by
        apply l_exist_min_nonpos _
        show ∃ t, b t ≤ 0
        by_contra! h_contra
        have : ∀ t, b (2 * (t + 1)) < b (2 * t) := by
          intro t
          rw [mul_add, mul_one, h_b]
          exact Int.sub_lt_self (b (2 * t)) (h_contra (2 * t + 1))
        obtain ⟨t, ht⟩ := l_exist_nonpos (fun t => b (2 * t)) this
        linarith only [h_contra (2 * t), ht]
      obtain ⟨t, ⟨h_btnonpos, h_iltt⟩⟩ := this

      -- t > 1
      have h_tgt1 : t > 1 := by
        by_contra!
        interval_cases t
        . rw [h_b0] at h_btnonpos
          linarith only [h_mgtone, h_btnonpos]
        . linarith only [h_btnonpos, h_b1pos]

      -- forall i ∈ [0, t - 1], b i ∈ rg
      have h_biinrg : ∀ i ≤ t - 1, b i ∈ rg := by
        intro i hi
        have ⟨hn, hm, hmn⟩ := h_valid
        rw [h_defrg, Finset.mem_Icc] at hm hn
        simp only [h_defrg, Finset.mem_Icc, show 1 ≤ b i by linarith only [h_iltt i (by omega)], true_and]
        induction' i using Nat.strong_induction_on with i ih
        match i with
        | 0 =>
          linarith [b, a, hm]
        | 1 =>
          linarith [b, a, hm, hn]
        | x + 2 =>
          rw [h_b]
          specialize ih x (by linarith only) (by linarith only [hi])
          have : x + 1 < t := by
            zify
            zify at hi
            rw [Nat.cast_sub (show 1 ≤ t by linarith only [h_tgt1]), Nat.cast_one] at hi
            linarith only [hi]
          apply h_iltt (x + 1) at this
          omega

      use t - 2
      rw [show t - 2 + 1 = t - 1 by omega]

      -- (b (t - 1), b (t - 2)) is valid
      have h_val : valid_prop (b (t - 1)) (b (t - 2)) := by
        have : ∀ i ≤ t - 2 + 1, b i ∈ rg := by
          intro i hi
          exact h_biinrg _ (by omega)
        convert l_1 (t - 2) this using 1
        congr; omega

      -- so 1 ≤ b (t - 1)
      have h_le : 1 ≤ b (t - 1) := h_iltt _ (sub_one_lt_of_lt h_tgt1)

      rcases Int.le_iff_eq_or_lt.mp h_btnonpos with hbt | hbt
      -- If b t = 0, then b (t - 1) = b (t - 2)
      . have heq : b (t - 1) = b (t - 2) := by
          specialize h_b (t - 2)
          rw [Nat.sub_add_cancel h_tgt1, show t - 2 + 1 = t - 1 by omega, hbt] at h_b
          linarith only [h_b]
        rcases LE.le.eq_or_gt h_le with h | h
        -- if b (t - 1) = 1, then we done
        . simp only [h, ← heq, true_and]
          exact h_biinrg
        -- if b (t - 1) > 1, then b (t - 2) must be greater than b (t - 1), which gives a contradiction
        . specialize t2 (b (t - 1)) h (b (t - 2)) h_val
          simp only [heq, lt_self_iff_false] at t2

      -- If b t < 0, we have b(t - 2) < b (t - 1) contradicts to '(b (t - 1), b (t - 2)) is valid'
      . have hlt : b (t - 2) < b (t - 1) := by
          specialize h_b (t - 2)
          rw [Nat.sub_add_cancel h_tgt1, show t - 2 + 1 = t - 1 by omega] at h_b
          rw [h_b] at hbt
          exact Int.lt_of_sub_neg hbt
        rcases LE.le.eq_or_gt h_le with h | h
        . rw [h] at h_val
          specialize t1 (b (t - 2)) h_val
          rcases t1 with h' | h' <;> linarith only [hlt, h, h']
        . specialize t2 (b (t - 1)) h (b (t - 2)) h_val
          linarith only [hlt, t2]

    obtain ⟨u, ⟨h_bup1, h_bu, _⟩⟩ := this

    -- so the sequence b is exactly the Fibonacci sequence
    have h_b_fib : ∀ i ≤ (u + 1), b i = fib (u + 2 - i) := by
      have : ∀ i ≤ (u + 1), b (u + 1 - i) = fib (i + 1) := by
        intro i hi
        induction' i using Nat.strong_induction_on with i ih
        match i with
        | 0 =>
          norm_num [h_bup1]
        | 1 =>
          norm_num [h_bu]
        | t + 2 =>
          have r1 := ih (t + 1) (Nat.lt_add_one (t + 1)) (le_of_succ_le hi)
          have r2 := ih t (show t < t + 2 by linarith only) (show t ≤ u + 1 by linarith only [hi])
          specialize h_b (u - t - 1)
          rw [show u - t - 1 + 1 = u + 1 - (t + 1) by omega,
              show u - t - 1 + 2 = u + 1 - t by omega,
              r1, r2] at h_b
          rw [show u + 1 - (t + 2) = u - t - 1 by omega, fib_add_two, Nat.cast_add]
          linarith only [h_b]
      intro i hi
      specialize this (u + 1 - i) (sub_le (u + 1) i)
      convert this using 1
      all_goals congr; omega

    -- Therefore, all the solutions of the equation are given as two consecutive members of the Fibonacci sequence
    have h_eqm : m = fib (u + 2) := by
      have := h_b_fib 0 (Nat.le_add_left 0 (u + 1))
      rw [tsub_zero] at this
      norm_num [← this, b, a]
    have h_eqn : n = fib (u + 3) := by
      have := h_b_fib 1 (by linarith)
      norm_num [b] at this
      rw [fib_add_two, Nat.cast_add, ← h_eqm, ← this]
      ring
    use u + 2

  dsimp only [IsGreatest]
  constructor

  -- verify thatn 55 ^ 2 + 89 ^ 2 is reachable
  . show 55 ^ 2 + 89 ^ 2 ∈ s
    rw [h_defs, h_defrg, Set.mem_setOf_eq]
    use 55
    norm_num
    use 89
    norm_num

  -- proof that 55 ^ 2 + 89 ^ 2 is upperbound
  . show 55 ^ 2 + 89 ^ 2 ∈ upperBounds s
    simp only [upperBounds, h_defs, h_defrg, Finset.mem_Icc, Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro v m h_mge h_mle n h_nge h_nle h_eq h_eqv
    rw [← h_eqv]
    have : valid_prop m n := by
      simp only [valid_prop, h_defrg, h_mge, h_mle, h_nge, h_nle, h_eq, Finset.mem_Icc, true_and]
    obtain ⟨k, ⟨hmv, hnv⟩⟩ := t4 m n this

    have : k ≤ 10 := by
      by_contra! h_contra
      have : fib (k + 1) < fib 12 := by
        norm_num
        zify
        linarith
      have : k + 1 < 12 := (fib_lt_fib (show 2 ≤ k + 1 by linarith only [h_contra])).mp this
      linarith only [this, h_contra]

    rw [hmv, hnv]
    interval_cases k
    all_goals norm_num
