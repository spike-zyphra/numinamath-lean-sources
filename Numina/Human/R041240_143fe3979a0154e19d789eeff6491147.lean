import Mathlib

open Classical

/- The sequence $a_{0}, a_{1}, a_{2}, \ldots$ of positive integers satisfies  $$ a_{n+1}=\left\{\begin{array}{ll} \sqrt{a_{n}}, & \text { if } \sqrt{a_{n}} \text { is an integer } \\ a_{n}+3, & \text { otherwise } \end{array} \quad \text { for every } n \geqslant 0\right. $$  Determine all values of $a_{0}>1$ for which there is at least one number $a$ such that $a_{n}=a$ for infinitely many values of $n$. (South Africa) Answer: All positive multiples of 3. -/
theorem number_theory_25071 (a : ℕ → ℕ → ℕ)
    (h₀ : ∀ a₀, a a₀ 0 = a₀)
    (hsucc : ∀ a₀, ∀ n, a a₀ (n + 1) = if IsSquare (a a₀ n) then Nat.sqrt (a a₀ n) else a a₀ n + 3) :
    {a₀ | 1 < a₀ ∧ (∀ n, a a₀ n > 0) ∧ ∃ a' : ℕ, {n : ℕ | a a₀ n = a'}.Infinite} = {3 * k | k > 0 } := by

  have hpos {a₀ n : ℕ} (han : a a₀ n > 0) : ∀ m ≥ n, a a₀ m > 0 := by
    intro m hm
    induction m, hm using Nat.le_induction
    · exact han
    · rename_i m hm ih
      rw [hsucc]
      by_cases h : IsSquare (a a₀ m)
      · simp [h]
        exact Nat.sqrt_pos.mpr ih
      · simp [h]
  have hgt1 {a₀ n : ℕ} (han : a a₀ n > 1) : ∀ m ≥ n, a a₀ m > 1 := by
    intro m hm
    induction m, hm using Nat.le_induction
    · exact han
    · rename_i m hm ih
      rw [hsucc]
      by_cases h : IsSquare (a a₀ m)
      · simp [h]
        obtain ⟨y, hy⟩ := h
        rw [hy, ←sq, Nat.sqrt_eq']
        rw [hy, ←sq] at ih
        by_contra h
        simp at h
        interval_cases y
        all_goals simp at ih
      · simp [h]
  -- Since the value of $a_{n+1}$ only depends on the value of $a_{n}$,
  -- if $a_{n}=a_{m}$ for two different indices $n$ and $m$,
  -- then the sequence is eventually periodic.
  let eventually_periodic (f : ℕ → ℕ) : Prop := ∃ m n, m < n ∧ f m = f n
  have add_eq_add_of_eq {a₀ m n k : ℕ} (h : a a₀ m = a a₀ n) : a a₀ (m + k) = a a₀ (n + k) := by
    induction k with
    | zero => simp [h]
    | succ h ih =>
      rw [←add_assoc, ←add_assoc, hsucc, hsucc]
      · congr
  have eq_of_eventually_periodic {a₀ : ℕ} (N : ℕ) (hf : eventually_periodic (a a₀)) : ∃ m n, N < m ∧ m < n ∧ a a₀ m = a a₀ n := by
    obtain ⟨m, n, hlt, heq⟩ := hf
    use m + 1 + N, n + 1 + N
    simp [hlt]
    rw [add_assoc, add_assoc]
    exact add_eq_add_of_eq heq
  -- So we look for the values of $a_{0}$ for which the sequence is eventually periodic.
  have infinite_iff_eventually_periodic {a₀ : ℕ} : (∃ a' : ℕ, {n : ℕ | a a₀ n = a'}.Infinite) ↔ eventually_periodic (a a₀) := by
    constructor <;> intro h
    · obtain ⟨a', ha'⟩ := h
      let p := fun n => a a₀ n = a'
      let m := Nat.nth p 0
      let n := Nat.nth p 1
      have hp : (setOf p).Infinite := by exact ha'
      use m, n
      constructor
      · apply Nat.nth_lt_nth hp |>.mpr
        simp
      · have hm : p m := by apply Nat.nth_mem_of_infinite hp
        have hn : p n := by apply Nat.nth_mem_of_infinite hp
        rw [hm, hn]
    · obtain ⟨m, n, hlt, heq⟩ := h
      use a a₀ m
      refine Set.infinite_of_forall_exists_gt ?_
      intro N
      use m + (N + 1) * (n - m)
      simp
      constructor
      · generalize (N + 1) = k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [←ih, add_comm k 1, add_mul, one_mul, ←add_assoc, Nat.add_sub_cancel']
          · exact add_eq_add_of_eq (id (Eq.symm heq))
          · exact Nat.le_of_succ_le hlt
      · apply Nat.lt_add_left
        rw [add_mul]
        apply lt_add_of_le_of_pos
        · refine Nat.le_mul_of_pos_right N ?_
          simp [hlt]
        · simp [hlt]

  --  Claim 1. If $a_{n} \equiv-1(\bmod 3)$, then, for all $m&gt;n, a_{m}$ is not a perfect square.
  have not_square_of_mod_eq_two {a₀ n : ℕ} (han : a a₀ n ≡ 2 [MOD 3]) (m : ℕ) (hm : m ≥ n) : ¬ IsSquare (a a₀ m) := by
    -- A square cannot be congruent to -1 modulo 3 ,
    have hsq {x : ℕ} (hx : x ≡ 2 [MOD 3]) : ¬ IsSquare x := by
      by_contra hsq
      obtain ⟨y, hy⟩ := hsq
      let t := y / 3
      let s := y % 3
      have : y = 3 * t + s := by exact Eq.symm (Nat.div_add_mod y 3)
      rw [this] at hy
      have : s ^ 2 - (2 : ℤ) ≡ 0 [ZMOD 3] := by
        trans x - 2
        · rw [hy, sq]
          apply Int.ModEq.sub_right
          simp
          apply Int.ModEq.mul
          all_goals (
            trans 0 + s
            · congr; ring
            · apply Int.ModEq.add
              · symm; apply Int.modEq_of_dvd; simp
              · exact rfl
          )
        · refine Dvd.dvd.modEq_zero_int ?_
          use x / 3
          apply sub_eq_of_eq_add
          norm_cast
          have : x % 3 = 2 := by exact hx
          rw [←this]
          exact Eq.symm (Nat.div_add_mod x 3)
      apply Int.ModEq.dvd at this
      have hs : s < 3 := by apply Nat.mod_lt; simp
      interval_cases s
      all_goals norm_num at this
    have strong_version : ¬ IsSquare (a a₀ m) ∧ a a₀ m ≡ 2 [MOD 3] := by
      induction m, hm using Nat.le_induction
      · -- so $a_{n} \equiv-1(\bmod 3)$ implies that $a_{n}$ is not a square,
        constructor
        · exact hsq han
        · exact han
      · rename_i m hm ih
        -- therefore $a_{n+1}=a_{n}+3&gt;a_{n}$.
        -- As a consequence, $a_{n+1} \equiv a_{n} \equiv-1(\bmod 3)$, so $a_{n+1}$ is not a square either.
        rw [hsucc]
        simp [ih]
        have : a a₀ m + 3 ≡ 2 [MOD 3] := by
          trans 2 + 3
          · apply Nat.ModEq.add_right
            exact ih.2
          · apply Nat.modEq_of_dvd
            simp
        -- By repeating the argument, we prove that, from $a_{n}$ on,
        -- all terms of the sequence are not perfect squares and are greater than their predecessors,
        --  which completes the proof.
        constructor
        · exact hsq this
        · exact this
    exact strong_version.1

  -- It follows that the sequence is eventually strictly increasing
  have increasing_of_mod_eq_two {a₀ n : ℕ} (han : a a₀ n ≡ 2 [MOD 3]) (m : ℕ) (hm : m ≥ n) : (a a₀ m : ℤ) = a a₀ n + 3 * (m - n) := by
    induction m, hm using Nat.le_induction
    · simp
    · rename_i m hm ih
      rw [hsucc, if_neg (not_square_of_mod_eq_two han m hm)]
      simp [ih]
      ring
  -- so it is not eventually periodic.
  have not_eventually_periodic_of_mod_eq_two {a₀ n : ℕ} (han : a a₀ n ≡ 2 [MOD 3]) : ¬ eventually_periodic (a a₀) := by
    intro he
    apply eq_of_eventually_periodic n at he
    obtain ⟨m, m', hlt, hm, heq⟩ := he
    apply Int.natCast_inj.mpr at heq
    rw [increasing_of_mod_eq_two han m, increasing_of_mod_eq_two han m'] at heq
    · simp at heq
      simp [heq] at hm
    · apply le_of_lt
      exact Nat.lt_trans hlt hm
    · exact le_of_lt hlt

  -- Claim 2. If $a_{n} \not \equiv-1(\bmod 3)$ and $a_{n}&gt;9$ then there is an index $m&gt;n$ such that $a_{m}&lt;a_{n}$.
  have decreasing_of_mod_ne_two {a₀ n : ℕ} (han : ¬ a a₀ n ≡ 2 [MOD 3]) (han' : a a₀ n > 9) : ∃ m > n, a a₀ m < a a₀ n := by
    -- Proof. Let $t^{2}$ be the largest perfect square which is less than $a_{n}$.
    let t := Nat.sqrt (a a₀ n)
    -- Since $a_{n}&gt;9, t$ is at least 3.
    have ht : t ≥ 3 := by
      by_contra h
      simp at h
      apply Nat.sqrt_lt'.mp at h
      simp at h
      linarith
    -- The first square in the sequence $a_{n}, a_{n}+3, a_{n}+6, \ldots$ will be $(t+1)^{2},(t+2)^{2}$ or $(t+3)^{2}$,
    let b : ℕ := (t + (3 - (a a₀ n + t) % 3)) ^ 2
    have htleb : (t + 1) ^ 2 ≤ b := by 
      apply Nat.pow_le_pow_left
      simp
      apply Nat.le_sub_of_add_le
      rw [show 3 = 1 + 2 by rfl]
      apply Nat.add_le_add_left
      simp
      apply Nat.le_of_lt_succ
      apply Nat.mod_lt
      simp
    have hleb : a a₀ n ≤ b := by
      trans (t + 1) ^ 2
      · apply le_of_lt
        exact Nat.lt_succ_sqrt' (a a₀ n)
      · exact htleb
    have : 3 ∣ (b : ℤ) - a a₀ n := by
      unfold b
      rw [Nat.add_mod]
      mod_cases ha : a a₀ n % 3
      · have : a a₀ n % 3 = 0 := by exact ha
        simp [this]
        apply Dvd.dvd.sub
        · apply Dvd.dvd.pow
          rw [Nat.cast_sub]
          · rw [←Int.add_sub_assoc, add_comm, Int.add_sub_assoc]
            apply Dvd.dvd.add
            · simp
            · rw [←Nat.cast_sub]
              norm_cast
              apply Nat.dvd_sub_mod
              exact Nat.mod_le t 3
          · apply le_of_lt
            apply Nat.mod_lt
            simp
          · simp
        · norm_cast
          apply Nat.dvd_of_mod_eq_zero
          exact this
      · have : a a₀ n % 3 = 1 := by exact ha
        apply Nat.modEq_iff_dvd.mp
        simp [this]
        trans 2 ^ 2
        · simp
          exact ha
        · apply Nat.ModEq.pow
          · trans 2 + (t + 1 - (t + 1) % 3)
            · trans 2 + 0
              · simp; rfl
              · apply Nat.ModEq.add_left
                apply Nat.modEq_of_dvd
                simp
                norm_cast
                apply Nat.dvd_sub_mod
            · congr 1
              rw [←Nat.add_sub_assoc, ←Nat.add_sub_assoc]
              · ring_nf
              · apply le_of_lt
                apply Nat.mod_lt
                simp
              · exact Nat.mod_le (t + 1) 3
      · exact han.elim ha
    rw [←Nat.cast_sub hleb] at this
    norm_cast at this
    obtain ⟨u, hu⟩ := this
    have : IsSquare (a a₀ n + 3 * u) := by
      use t + (3 - (a a₀ n + t) % 3)
      rw [←hu, Nat.add_sub_cancel']
      · ring
      · trans (t + 1) ^ 2
        · apply le_of_lt; exact Nat.lt_succ_sqrt' (a a₀ n)
        · exact htleb
    have : ∃ m ≥ n, IsSquare (a a₀ m) ∧ a a₀ m ≤ b := by
      let p (x : ℕ) : Prop := ∃ k, a a₀ n + 3 * k = x ∧ IsSquare x
      have hp : ∃ x, p x := by use a a₀ n + 3 * u, u
      let r := Nat.find hp
      obtain ⟨k, hk, hsq⟩ := Nat.find_spec hp
      have {m : ℕ} (hm : m ≥ n) (hm' : m - n < k) : ¬ IsSquare (a a₀ m) ∧ a a₀ (m + 1) = a a₀ n + 3 * (m + 1 - n) := by
        induction m, hm using Nat.le_induction
        · simp at hm'
          have : a a₀ n < r := by
            unfold r
            rw [←hk]
            simp
            exact hm'
          apply Nat.lt_find_iff hp _ |>.mp at this
          simp [p] at this
          have : ¬IsSquare (a a₀ n) := by
            apply this (x := 0)
            · simp
            · simp
          simp [hsucc, this]
        · rename_i m hm ih
          have : m - n < k := by apply lt_of_le_of_lt ?_ hm'; simp; rw [Nat.sub_add_cancel]; simp; exact Nat.le_add_right_of_le hm
          apply ih at this
          have nsq : ¬ IsSquare (a a₀ (m + 1)) := by
            rw [this.2]
            have : a a₀ n + 3 * (m + 1 - n) < r := by
              unfold r
              rw [←hk]
              simp
              exact hm'
            apply Nat.lt_find_iff hp _ |>.mp at this
            simp [p] at this
            obtain h := this (a a₀ n + 3 * (m + 1 - n)) (by simp) (m + 1 - n)
            apply h
            ring
          use nsq
          rw [hsucc, if_neg nsq, this.2]
          rw [add_assoc]
          congr 1
          rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_add, Nat.mul_add, Nat.mul_add]
          simp
          nth_rw 2 [Nat.sub_add_comm]
          trans 3 * m
          · simp; exact hm
          · simp
      use n + k
      constructor
      · exact Nat.le_add_right n k
      · have : a a₀ (n + k) = a a₀ n + 3 * k := by
          by_cases hk : k = 0
          · simp [hk]
          · have hk : k > 0 := by exact Nat.zero_lt_of_ne_zero hk
            have hge : n + k - 1 ≥ n := by
              rw [Nat.add_sub_assoc]
              simp
              exact hk
            have hlt : n + k - 1 - n < k := by
              apply Nat.sub_lt_left_of_lt_add
              · exact hge
              · simp [hk]
            obtain h := this hge hlt
            rw [Nat.sub_add_cancel] at h
            rw [h.2, Nat.add_sub_cancel_left]
            exact le_add_of_le_right hk
            
        rw [this]
        constructor
        · rw [hk]; exact hsq
        · rw [hk]
          apply Nat.find_le
          simp [p]
          constructor
          · use u
            rw [←hu, Nat.add_sub_cancel']
            exact hleb
          · use t + (3 - (a a₀ n + t) % 3)
            ring
    -- therefore there is an index $m&gt;n$ such that $a_{m} \leqslant t+3&lt;t^{2}&lt;a_{n}$, as claimed.
    obtain ⟨m, hm, hsq, hlt⟩ := this
    have : a a₀ (m + 1) ≤ t + (3 - (a a₀ n + t) % 3) := by
      rw [hsucc]
      simp [hsq]
      obtain ⟨y, hy⟩ := hsq
      rw [hy, ←sq] at hlt
      rw [hy, ←sq, Nat.sqrt_eq']
      by_contra h
      push_neg at h
      have : ¬ y ^ 2 ≤ b := by
        push_neg
        unfold b
        apply Nat.pow_lt_pow_left
        · exact h
        · simp
      exact this.elim hlt
    use m + 1
    constructor
    · exact Order.lt_add_one_iff.mpr hm
    · apply lt_of_le_of_lt this
      apply lt_of_le_of_lt (b := t + 3)
      · rw [←Nat.add_sub_assoc]
        · exact Nat.sub_le (t + 3) ((a a₀ n + t) % 3)
        · apply le_of_lt
          refine Nat.mod_lt (a a₀ n + t) ?h.right.hab.h.hab.a
          simp
      · apply lt_of_lt_of_le (b := t ^ 2)
        · nlinarith
        · exact Nat.sqrt_le' (a a₀ n)

  -- Claim 3. If $a_{n} \equiv 0(\bmod 3)$, then there is an index $m&gt;n$ such that $a_{m}=3$.
  have eq_3_of_mod_eq_zero {a₀ n : ℕ} (han : a a₀ n ≡ 0 [MOD 3]) (han' : a a₀ n > 0) : ∃ m > n, a a₀ m = 3 := by
    -- Proof. First we notice that, by the definition of the sequence, a multiple of 3 is always followed by another multiple of 3 .
    have h3dvd : ∀ m ≥ n, 3 ∣ a a₀ m := by
      intro m hm
      induction m, hm using Nat.le_induction
      · exact Nat.dvd_of_mod_eq_zero han
      · rename_i m hm ih
        rw [hsucc]
        by_cases h : IsSquare (a a₀ m)
        · simp [h]
          obtain ⟨y, hy⟩ := h
          rw [hy, ←sq, Nat.sqrt_eq']
          rw [hy, ←sq] at ih
          apply Prime.dvd_of_dvd_pow ?_ ih
          refine Nat.prime_iff.mp ?_
          norm_num
        · simp [h]
          exact ih
    let p (x : ℕ) : Prop := ∃ m > n, a a₀ m = x
    have hp : ∃ x, p x := by use a a₀ (n + 1), n + 1; simp
    -- let $j$ be an index such that $a_{j}$ is equal to the minimum value of the set $\left\{a_{n+1}, a_{n+2}, \ldots\right\}$.
    obtain hr := Nat.find_spec hp
    unfold p at hr
    obtain ⟨m, hm, heq⟩ := hr
    have ⟨t, ht⟩ := h3dvd m (le_of_lt hm)
    have nsq3 : ¬ IsSquare 3 := by
      intro h
      obtain ⟨k, hk⟩ := h
      have : k ≤ 2 := by
        by_contra h
        simp at h
        have : k * k > 2 * 2 := by exact Nat.mul_lt_mul_of_lt_of_lt h h
        rw [←hk] at this
        simp at this
      interval_cases k
      all_goals simp at hk
    have nsq6 : ¬ IsSquare 6 := by
      intro h
      obtain ⟨k, hk⟩ := h
      have : k ≤ 3 := by
        by_contra h
        simp at h
        have : k * k > 3 * 3 := by exact Nat.mul_lt_mul_of_lt_of_lt h h
        rw [←hk] at this
        simp at this
      interval_cases k
      all_goals simp at hk
    by_cases ht' : t ≤ 3
    · -- If $a_{n} \in\{3,6,9\}$ the sequence will eventually follow the periodic pattern $3,6,9,3,6,9, \ldots$ If $a_{n}&gt;9$,
      interval_cases t
      · simp at ht
        obtain hpos := hpos han' m (le_of_lt hm)
        simp [ht] at hpos
      · simp at ht
        have : a a₀ (m + 1) = 6 := by simp [hsucc, ht, nsq3]
        have : a a₀ (m + 2) = 9 := by rw [hsucc, this]; simp[nsq6]
        have : a a₀ (m + 3) = 3 := by rw [hsucc, this]; norm_num; use 3
        use m + 3
        simp [this]
        exact Nat.lt_add_right 3 hm
      · simp at ht
        have : a a₀ (m + 1) = 9 := by rw [hsucc, ht]; simp[nsq6]
        have : a a₀ (m + 2) = 3 := by rw [hsucc, this]; norm_num; use 3
        use m + 2
        simp [this]
        exact Nat.lt_add_right 2 hm
      · simp at ht
        use m + 1
        rw [hsucc, ht]
        norm_num
        constructor
        · exact Nat.lt_add_right 1 hm
        · use 3
    · -- We must have $a_{j} \leqslant 9$,
      -- otherwise we could apply Claim 2 to $a_{j}$ and get a contradiction on the minimality hypothesis.
      -- It follows that $a_{j} \in\{3,6,9\}$, and the proof is complete.
      simp at ht'
      have ht' : a a₀ m > 9 := by rw [ht]; linarith
      have han'' : ¬ a a₀ m ≡ 2 [MOD 3] := by
        intro h
        obtain han := h3dvd m (le_of_lt hm)
        apply Nat.mod_eq_zero_of_dvd at han
        have han : a a₀ m ≡ 0 [MOD 3] := by exact han
        apply Nat.ModEq.trans (Nat.ModEq.symm h) at han
        apply Nat.ModEq.dvd at han
        norm_cast at han
      apply decreasing_of_mod_ne_two han'' at ht'
      obtain ⟨m', hm', hlt'⟩ := ht'
      rw [heq] at hlt'
      apply Nat.lt_find_iff hp _ |>.mp at hlt'
      simp [p] at hlt'
      obtain h := hlt' (a a₀ m') (by simp) m'
      simp at h
      have : ¬ m' ≤ n := by
        simp
        exact Nat.lt_trans hm hm'
      exact this.elim h

  have eventually_periodic_of_mod_eq_zero {a₀ n : ℕ} (han : a a₀ n ≡ 0 [MOD 3]) (han' : a a₀ n > 0) : eventually_periodic (a a₀) := by
    obtain ⟨m, hlt, hm⟩ := eq_3_of_mod_eq_zero han han'
    have : a a₀ m ≡ 0 [MOD 3] := by rw [hm]; exact rfl
    obtain ⟨m', hlt', hm'⟩ := eq_3_of_mod_eq_zero this (hpos han' m (le_of_lt hlt))
    use m, m', hlt'
    rw [hm, hm']

  -- Claim 4. If $a_{n} \equiv 1(\bmod 3)$, then there is an index $m&gt;n$ such that $a_{m} \equiv-1(\bmod 3)$.
  have mod_eq_two_of_mod_eq_one {a₀ n : ℕ} (han : a a₀ n ≡ 1 [MOD 3]) (han' : a a₀ n > 1) : ∃ m > n, a a₀ m ≡ 2 [MOD 3] := by
    by_contra hmod
    push_neg at hmod
    -- by the definition of the sequence consists of non-multiples of 3 .
    have hmod3 : ∀ m ≥ n, a a₀ m ≡ 1 [MOD 3] := by
      intro m hm
      induction m, hm using Nat.le_induction
      · exact han
      · rename_i m hm ih
        mod_cases (a a₀ (m + 1)) % 3
        · rw [hsucc] at H
          by_cases h : IsSquare (a a₀ m)
          · simp [h] at H
            obtain ⟨y, hy⟩ := h
            rw [hy, ←sq, Nat.sqrt_eq'] at H
            rw [hy, ←sq] at ih
            have : y ^ 2 ≡ 0 [MOD 3] := by
              trans 0 ^ 2
              · apply Nat.ModEq.pow
                exact H
              · simp; rfl
            apply Nat.ModEq.trans (Nat.ModEq.symm ih) at this
            apply Nat.ModEq.dvd at this
            simp at this
            norm_num at this
          · simp [h] at H
            have : a a₀ m + 3 ≡ 1 + 3 [MOD 3] := by
              apply Nat.ModEq.add_right
              exact ih
            apply Nat.ModEq.trans (Nat.ModEq.symm H) at this
            apply Nat.ModEq.dvd at this
            simp at this
            norm_num at this
        · exact H
        · apply hmod (m + 1) (by exact Order.lt_add_one_iff.mpr hm) |>.elim H

    let p (x : ℕ) : Prop := ∃ m > n, a a₀ m = x
    have hp : ∃ x, p x := by use a a₀ (n + 1), n + 1; simp
    obtain hr := Nat.find_spec hp
    unfold p at hr
    obtain ⟨m, hm, heq⟩ := hr
    let t := a a₀ m / 3
    have ht : a a₀ m = 3 * t + 1 := by
      have : a a₀ m % 3 = 1 := by
        obtain h := hmod3 m (le_of_lt hm)
        exact h
      rw [←this]
      exact Eq.symm (Nat.div_add_mod (a a₀ m) 3)
    by_cases ht' : t ≤ 2
    · interval_cases t
      · simp at ht
        have : a a₀ m > 1 := by apply hgt1 han' m (le_of_lt hm)
        simp [ht] at this
      · -- Proof. In the sequence, 4 is always followed by $2 \equiv-1(\bmod 3)$,
        -- so the claim is true for $a_{n}=4$.
        simp at ht
        have : a a₀ (m + 1) = 2 := by
          rw [hsucc, ht]
          norm_num
          use 2
        have : a a₀ (m + 1) ≡ 2 [MOD 3] := by rw [this]
        exact (hmod (m + 1) (by simp; exact Nat.lt_add_right 1 hm)).elim this
      · -- If $a_{n}=7$, the next terms will be $10,13,16,4,2, \ldots$ and the claim is also true.
        simp at ht
        have : a a₀ (m + 1) = 10 := by
          rw [hsucc, ht]
          norm_num
          intro h
          obtain ⟨k, hk⟩ := h
          have : k ≤ 4 := by
            by_contra h
            simp at h
            have : k * k > 4 * 4 := by exact Nat.mul_lt_mul_of_lt_of_lt h h
            rw [←hk] at this
            simp at this
          interval_cases k
          all_goals (simp at hk)
        have : a a₀ (m + 2) = 13 := by
          rw [hsucc, this]
          norm_num
          intro h
          obtain ⟨k, hk⟩ := h
          have : k ≤ 4 := by
            by_contra h
            simp at h
            have : k * k > 4 * 4 := by exact Nat.mul_lt_mul_of_lt_of_lt h h
            rw [←hk] at this
            simp at this
          interval_cases k
          all_goals simp at hk
        have : a a₀ (m + 3) = 16 := by
          rw [hsucc, this]
          norm_num
          intro h
          obtain ⟨k, hk⟩ := h
          have : k ≤ 4 := by
            by_contra h
            simp at h
            have : k * k > 4 * 4 := by exact Nat.mul_lt_mul_of_lt_of_lt h h
            rw [←hk] at this
            simp at this
          interval_cases k
          all_goals simp at hk
        have : a a₀ (m + 4) = 4 := by
          rw [hsucc, this]
          norm_num
          use 4
        have : a a₀ (m + 5) = 2 := by
          rw [hsucc, this]
          norm_num
          use 2
        have : a a₀ (m + 5) ≡ 2 [MOD 3] := by rw [this]
        exact (hmod (m + 5) (by simp; exact Nat.lt_add_right 5 hm)).elim this
    · push_neg at ht'
      -- For $a_{n} \geqslant 10$, we again take an index $j&gt;n$
      -- such that $a_{j}$ is equal to the minimum value of the set $\left\{a_{n+1}, a_{n+2}, \ldots\right\}$,
      -- which by the definition of the sequence consists of non-multiples of 3 .
      -- Suppose $a_{j} \equiv 1(\bmod 3)$.
      -- Then we must have $a_{j} \leqslant 9$ by Claim 2 and the minimality of $a_{j}$.
      have : a a₀ m > 9 := by rw [ht]; linarith
      have han'' : ¬ a a₀ m ≡ 2 [MOD 3] := by apply hmod; exact hm
      apply decreasing_of_mod_ne_two han'' at this
      obtain ⟨m', hm', hlt'⟩ := this
      rw [heq] at hlt'
      apply Nat.lt_find_iff hp _ |>.mp at hlt'
      simp [p] at hlt'
      obtain h := hlt' (a a₀ m') (by simp) m'
      simp at h
      -- It follows that $a_{j} \in\{4,7\}$, so $a_{m}=2&lt;a_{j}$ for some $m&gt;j$,
      -- contradicting the minimality of $a_{j}$.
      -- Therefore, we must have $a_{j} \equiv-1(\bmod 3)$.
      have : ¬ m' ≤ n := by push_neg; exact Nat.lt_trans hm hm'
      exact this.elim h

  have not_eventually_periodic_of_mod_eq_one {a₀ n : ℕ} (han : a a₀ n ≡ 1 [MOD 3]) (han' : a a₀ n > 1) : ¬ eventually_periodic (a a₀) := by
    obtain ⟨m, hm⟩ := mod_eq_two_of_mod_eq_one han han'
    apply not_eventually_periodic_of_mod_eq_two (n := m)
    exact hm.2

  ext a₀
  simp
  mod_cases ha₀ : a₀ % 3
  · -- It follows from the previous claims that if $a_{0}$ is a multiple of 3 the sequence will eventually reach the periodic pattern
    -- $3,6,9,3,6,9, \ldots$;
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero ha₀
    by_cases h : k = 0
    · simp [h] at hk
      simp [hk]
    · apply Nat.pos_of_ne_zero at h
      have hgt : a₀ > 1 := by
        apply lt_of_lt_of_le (b := 3)
        · simp
        · rw [hk]
          exact Nat.le_mul_of_pos_right 3 h
      have : ∃ k, 0 < k ∧ 3 * k = a₀ := by
        use k, h
        exact Eq.symm hk
      simp [this, hgt]
      constructor
      · intro n
        induction n with
        | zero => rw [h₀]; exact Nat.zero_lt_of_lt hgt
        | succ n ih =>
          rw [hsucc a₀ n]
          split_ifs
          · exact Nat.sqrt_pos.mpr ih
          · exact Nat.add_pos_left ih 3
      · apply infinite_iff_eventually_periodic.mpr
        apply eventually_periodic_of_mod_eq_zero (n := 0)
        rw [h₀]
        exact ha₀
        rw [h₀]
        exact Nat.zero_lt_of_lt hgt
  · -- and if $a_{0} \equiv 1(\bmod 3)$ the sequence will be eventually strictly increasing.
    have : ¬ ∃ k, 0 < k ∧ 3 * k = a₀ := by
      push_neg
      intro k _ hk
      have : a₀ ≡ 0 [MOD 3] := by rw [←hk]; apply Nat.mod_eq_zero_of_dvd; exact Nat.dvd_mul_right 3 k
      have : 1 ≡ 0 [MOD 3] := by
        exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm this)) ha₀)
      apply Nat.dvd_of_mod_eq_zero at this
      simp at this
    simp only [this, iff_false, not_and]
    intro _ _
    apply Not.imp ?_ infinite_iff_eventually_periodic.mp
    apply not_eventually_periodic_of_mod_eq_one (n := 0)
    rw [h₀]
    exact ha₀
    apply hgt1 (n := 0)
    · rw [h₀]; assumption
    · simp
  · -- if $a_{0} \equiv-1(\bmod 3)$ the sequence will be strictly increasing;
    -- So the sequence will be eventually periodic if, and only if, $a_{0}$ is a multiple of 3 .
    have : ¬ ∃ k, 0 < k ∧ 3 * k = a₀ := by
      push_neg
      intro k _ hk
      have : a₀ ≡ 0 [MOD 3] := by rw [←hk]; apply Nat.mod_eq_zero_of_dvd; exact Nat.dvd_mul_right 3 k
      have : 2 ≡ 0 [MOD 3] := by
        exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm this)) ha₀)
      apply Nat.dvd_of_mod_eq_zero at this
      norm_num at this
    simp only [this, iff_false, not_and]
    intro _ _
    apply Not.imp ?_ infinite_iff_eventually_periodic.mp
    apply not_eventually_periodic_of_mod_eq_two (n := 0)
    rw [h₀]
    exact ha₀
