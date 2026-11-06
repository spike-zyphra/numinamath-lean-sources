import Mathlib

/- Suppose that $a_{0}, a_{1}, \ldots$ and $b_{0}, b_{1}, \ldots$ are two sequences of positive integers satisfying $a_{0}, b_{0} \geqslant 2$ and  $$ a_{n+1}=\operatorname{gcd}\left(a_{n}, b_{n}\right)+1, \quad b_{n+1}=\operatorname{lcm}\left(a_{n}, b_{n}\right)-1 $$  for all $n \geqslant 0$. Prove that the sequence $\left(a_{n}\right)$ is eventually periodic; in other words, there exist integers $N \geqslant 0$ and $t>0$ such that $a_{n+t}=a_{n}$ for all $n \geqslant N$. (France) -/
theorem number_theory_24649
  (a b : ℕ → ℤ)
  (h₀ : ∀ n, 0 < a n)
  (h₁ : ∀ n, 0 < b n)
  (h₂ : 2 ≤ a 0 ∧ 2 ≤ b 0)
  (h₃ : ∀ n, a (n + 1) = Int.gcd (a n) (b n) + 1)
  (h₄ : ∀ n, b (n + 1) = Int.lcm (a n) (b n) - 1)
  : (∃ N t, N ≥ 0 ∧ t > 0 ∧ ∀ n, N ≤ n → a (n + t) = a n) := by

  -- first we need to lemmas.

  -- 1. let a n be a sequence of nonnegative integers that is non-increasing,
  -- then for some sufficiently large N we have a n = a N for all n ≥ N.
  have stable_of_antitone (a : ℕ → ℤ) (h_nonneg : ∀ i, a i ≥ 0) (h_anti : Antitone a) :
  ∃ N, ∀ n ≥ N, a n = a N := by
    generalize h : a 0 = s
    -- we prove this lemma using induction on the first term a 0
    induction s
    case ofNat s =>
      induction' s with s ih generalizing a
      · -- if a 0 = 0 then every term a n = 0
        use 0
        intro n n_nonneg
        simp at h
        rw [h]
        have : a n ≤ 0 := by
          rw [← h]
          apply h_anti n_nonneg
        linarith [h_nonneg n]
      · -- if a n = s + 1 > 0, we consider two cases
        by_cases h_next : ∃ i, a i < a 0
        · -- case 1, there is a term a i < a 0
          obtain ⟨i, hi⟩ := h_next
          simp at h
          have : a i < s + 1 := by rw [← h]; exact hi
          have a_i_ub : a i ≤ s := by linarith
          -- we build a new sequence a' with a' j = a (j + i), and setting a' 0 = s
          let a' := fun j ↦ if j = 0 then ↑s else a (j + i)
          have a'_nonneg : ∀ i, a' i ≥ 0 := by
            intro i
            by_cases h' : i = 0
            all_goals unfold a'; simp [h']
            apply h_nonneg
          have a'_anti : Antitone a' := by
            intro j k jlek
            unfold a'
            by_cases h1 : k = 0
            all_goals by_cases h2 : j = 0
            all_goals simp [h1, h2]
            · linarith [Nat.zero_lt_of_ne_zero h2]
            · trans a i
              apply h_anti
              linarith
              exact a_i_ub
            · apply h_anti
              linarith
          have a'_0 : a' 0 = Int.ofNat s := by
            unfold a'; simp
          have ⟨N', hN'⟩ := ih a' a'_nonneg a'_anti a'_0
          by_cases hN'_0 : N' = 0
          · rw [hN'_0] at hN'
            unfold a' at hN'
            simp at hN'
            use i + 1
            intro n hn
            rw [add_comm, hN' 1 (by norm_num)]
            have : n - i ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr hn
            have hN'' := hN' (n - i) this
            have : n - i + i = n := by
              apply Nat.sub_add_cancel
              exact Nat.le_of_succ_le hn
            rw [← this]
            assumption
          unfold a' at hN'
          simp [hN'_0] at hN'
          use N' + i
          intro n n_ge
          have : n - i ≥ N' := Nat.le_sub_of_add_le n_ge
          have h_eq' := hN' (n - i) this
          have : n - i ≠ 0 := by
            by_contra h
            rw [h] at this
            have : N' = 0 := by exact Nat.eq_zero_of_le_zero this
            contradiction
          simp [this] at h_eq'
          have : n - i + i = n := by
            apply Nat.sub_add_cancel
            linarith
          rw [← this]
          assumption
        · -- case 2, every term equals a 0, then we are done
          push_neg at h_next
          use 0
          intro n n_nonneg
          have : a n ≤ a 0 := h_anti n_nonneg
          linarith [h_next n]
    case negSucc s =>
      have : a 0 < 0 := by
        rw [h]; exact Int.negSucc_lt_zero s
      linarith [h_nonneg 0]

  -- 2. let f n be a sequence with f n = f n + 1, then all terms f n = f 0.
  have stable_of_eq_succ {α : Type} {f : ℕ → α} (hf : ∀ n, f n = f (n + 1)) : ∀ n, f n = f 0 := by
    intro n
    induction' n with n ih
    · rfl
    rwa [← hf]

  -- now we start the proof of the main theorem

  -- let s n = a n + b n
  let s := fun n ↦ a n + b n

  -- Notice that if a n ∣ b n, then a (n + 1) = a n + 1
  have lem_1_1 (n : ℕ) : a n ∣ b n ↔ a (n + 1) = a n + 1 := by
    constructor
    · intro h_dvd
      rw [h₃ n]
      congr
      have : Int.gcd (a n) (b n) = (a n).natAbs := by
        exact Int.gcd_eq_left h_dvd
      rw [this]
      refine Int.natAbs_of_nonneg ?H
      exact Int.le_of_lt (h₀ n)
    · intro h_succ
      rw [h₃ n] at h_succ
      have h_gcd_eq : Int.gcd (a n) (b n) = a n := by linarith
      rw [← h_gcd_eq]
      exact Int.gcd_dvd_right

  -- and if a n ∣ b n, then b (n + 1) = b n - 1
  have lem_1_2 (n : ℕ) : a n ∣ b n ↔ b (n + 1) = b n - 1 := by
    constructor

    · intro h_dvd
      rw [h₄ n]
      congr
      have : ↑(Int.lcm (a n) (b n)) ∣ (b n) := by
        apply Int.lcm_dvd h_dvd (Int.dvd_refl (b n))
      have : (b n) ∣ Int.lcm (a n) (b n) := by
        exact Int.dvd_lcm_right
      apply Int.dvd_antisymm
      exact Int.ofNat_zero_le ((a n).lcm (b n))
      exact Int.le_of_lt (h₁ n)
      repeat assumption
    · intro h_succ
      rw [h₄ n] at h_succ
      have h_lcm_eq : Int.lcm (a n) (b n) = b n := by linarith
      rw [← h_lcm_eq]
      exact Int.dvd_lcm_left

  -- and if a n ∣ b n, then s (n + 1) = s n
  have lem_1_3 (n : ℕ) : a n ∣ b n → s (n + 1) = s n := by
    intro h_dvd
    unfold s
    rw [lem_1_1 n |>.mp h_dvd, lem_1_2 n |>.mp h_dvd]
    ring

  -- Define W n as follows
  let W := fun n ↦ {m : ℤ | m ≥ a n ∧ ¬ m ∣ s n}
  -- let w n be the minimum element of W n
  let w := fun n ↦ sInf (W n)

  -- clearly W n is non-empty as (s n) + 1 ∈ W n
  have W_nonempty (n : ℕ) : (W n).Nonempty := by
    use (s n) + 1
    unfold W
    constructor
    · unfold s
      linarith [h₀ n, h₁ n]
    · intro h_dvd
      have : s n + 1 ≤ s n := by
        apply Int.le_of_dvd ?_ h_dvd
        unfold s
        linarith [h₀ n, h₁ n]
      unfold s at this
      simp at this

  -- also W n has a lower bound 0
  have W_bdd_below (n : ℕ) : BddBelow (W n) := by
    use 0
    intro x ⟨h, _⟩
    trans a n
    exact Int.le_of_lt (h₀ n)
    exact h

  -- observe that ¬ a n ∣ b n implies a n ∈ W n implies a n = w n
  have an_eq_wn_of_not_dvd_bn {n : ℕ} : ¬ a n ∣ b n → a n = w n := by
    intro h_dvd
    have h_not_dvd_sn : ¬ a n ∣ s n := by
      unfold s
      simp [h_dvd]
    have : a n ≤ w n := by
      apply le_csInf (W_nonempty n)
      exact fun _ x ↦ x.1
    have : w n ≤ a n := by
      unfold w
      apply csInf_le (W_bdd_below n)
      exact ⟨le_rfl, h_not_dvd_sn⟩
    linarith

  -- clearly w n ∈ W n
  have w_mem_W (n : ℕ) : w n ∈ W n := by
    exact Int.csInf_mem (W_nonempty n) (W_bdd_below n)

  -- Claim 1. the sequence (w n) is non-increasing
  have w_antitone : Antitone w := by
    refine antitone_nat_of_succ_le ?hf
    intro n
    by_cases h_dvd : a n ∣ b n
    · -- if a n ∣ b n, then a (n + 1) = a n + 1. Due to a n ∣ s n, we have a n ∉ W n.
      -- Moreover s (n + 1) = s n, therefore W (n + 1) = W n. So w (n + 1) = w n
      have : W (n + 1) = W n := by
        unfold W
        rw [lem_1_1 n |>.mp h_dvd]
        rw [lem_1_3 n h_dvd]
        ext x
        constructor
        · simp; exact fun h1 h2 ↦ ⟨Int.le_of_lt h1, h2⟩
        · simp
          intro h1 h2
          constructor
          · have : x ≠ a n := by
              by_contra h
              unfold s at h2
              rw [h] at h2
              simp [h_dvd] at h2
            have : x > a n := by exact lt_of_le_of_ne h1 (id (Ne.symm this))
            exact this
          · exact h2
      unfold w
      rw [this]
    · -- if ¬ a n ∣ b n, then we have shown that w n = a n
      rw [← an_eq_wn_of_not_dvd_bn h_dvd]

      -- we show that a n ∈ W (n + 1), this implies that w (n + 1) ≤ a n = w n
      have : a n ∈ W (n + 1) := by
        constructor
        · -- we need that a n ≥ a (n + 1), this holds as gcd(a n, b n) < a n
          rw [h₃ n]
          apply Int.add_one_le_iff.mpr
          apply lt_of_le_of_ne
          · have : ↑(Int.gcd (a n) (b n)) ∣ a n := by
              exact Int.gcd_dvd_left
            exact Int.le_of_dvd (h₀ n) this
          · intro h
            rw [← h] at h_dvd
            have : ↑(Int.gcd (a n) (b n)) ∣ b n := by
              exact Int.gcd_dvd_right
            contradiction
        · -- we also need ¬ a n ∣ s (n + 1), note that s (n + 1) = gcd(a n, b n) + lcm(a n, b n)
          -- observe that a n divides lcm(a n, b n) but not gcd(a n, b n).
          unfold s
          rw [h₃ n, h₄ n]
          intro h_dvd_s
          simp at h_dvd_s
          have : a n ∣ Int.lcm (a n) (b n) := by
            exact Int.dvd_lcm_left
          have : a n ∣ Int.gcd (a n) (b n) := by
            exact (Int.dvd_iff_dvd_of_dvd_add h_dvd_s).mpr this
          have : ↑(Int.gcd (a n) (b n)) ∣ b n := by
            exact Int.gcd_dvd_right
          have : a n ∣ b n := by
            trans ↑(Int.gcd (a n) (b n))
            repeat assumption
          contradiction

      exact csInf_le (W_bdd_below (n + 1)) this

  -- we need that w i > 0 for all i
  have w_pos : ∀ i, w i > 0 := by
    intro i
    suffices h : w i ≥ 1 by linarith
    unfold w
    apply le_csInf
    exact W_nonempty i
    intro b ⟨h, _⟩
    linarith [h₀ i]

  have w_nonneg : ∀ i, w i ≥ 0 := fun i ↦ Int.le_of_lt (w_pos i)

  -- so w n is a non-increaseing sequence of positive numbers
  -- by our first lemma it stables after some index N. Let w₀ := w N
  have ⟨N, h_w_stable_N⟩:= stable_of_antitone w w_nonneg w_antitone
  let w₀ := w N

  -- we show that if a n < w₀ then a n ∣ b n, this will imply that a (n + 1) = a n + 1
  -- using lem_1_1
  have an_dvd_bn_of_lt_w₀ (n : ℕ) (n_ge : n ≥ N) : a n < w₀ → a n ∣ b n := by
    intro h_an_le_w₀
    by_contra h_not_dvd_bn
    rw [an_eq_wn_of_not_dvd_bn h_not_dvd_bn, h_w_stable_N n n_ge] at h_an_le_w₀
    unfold w₀ at h_an_le_w₀
    linarith

  -- also, w₀ is an upper bound of the tail sequence a (n ≥ N)
  have an_le_w₀ : ∀ n ≥ N, a n ≤ w₀ := by
    intro n n_ge_N
    trans w n
    apply le_csInf (W_nonempty n)
    exact fun _ hmem ↦ hmem.1
    exact w_antitone n_ge_N

  -- Define g n = gcd(w₀, s n)
  let g := fun n ↦ Int.gcd w₀ (s n)

  -- we have that each term in g is non_zero.
  have g_nonzero : ∀ n, g n ≠ 0 := by
    intro n g_eq_0
    unfold g at g_eq_0
    apply Int.gcd_eq_zero_iff.mp at g_eq_0
    have : a n + b n = 0 := by
      unfold s at g_eq_0
      exact g_eq_0.2
    linarith [h₀ n, h₁ n]

  -- we show that the sequence g also stablizes after index N
  have h_g_stable_N : ∀ n ≥ N, g n = g N := by
    let g' := fun n ↦ g (n + N)
    -- this is done by show that g n = g (n + 1) for n ≥ N
    have : ∀ n, g' n = g' (n + 1) := by
      unfold g' g
      intro n
      rw [show n + 1 + N = n + N + 1 by ring]
      generalize h : n + N = n'
      have n'_ge_N : n' ≥ N := by linarith
      by_cases h_dvd : a n' ∣ b n'
      · -- a n' ∣ b n', then s (n + 1) = s n, so g (n + 1) = g n
        rw [lem_1_3 n' h_dvd]
      · -- ¬ a n' ∣ b n', then a n = w₀
        have an'_eq_w₀ : a n' = w₀ := by
          trans w n'
          · exact an_eq_wn_of_not_dvd_bn h_dvd
          exact h_w_stable_N n' n'_ge_N

        -- and gcd(a n, b n) = gcd(a n, s n) = gcd(w₀, s n)
        have h_g_eq_gcd : Int.gcd (a n') (b n') = g n' := by
          have : Int.gcd (a n') (b n') = Int.gcd (a n') (s n') := by
            unfold s Int.gcd
            rw [Int.natAbs_add_of_nonneg]
            exact Eq.symm (Nat.gcd_self_add_right (a n').natAbs (b n').natAbs)
            all_goals linarith [h₀ n', h₁ n']
          unfold g
          rw [this, an'_eq_w₀]

        -- we compute that s (n + 1) = g n + (w * (s n - w) / g n) * w
        have : s (n' + 1) = g n' + w₀ * (s n' - w₀) / g n' := by
          unfold s
          rw [h₃ n', h₄ n']
          simp [h_g_eq_gcd]
          simp [an'_eq_w₀]
          refine Int.eq_ediv_of_mul_eq_right ?H1 ?H2
          · norm_cast
            exact g_nonzero n'
          rw [← h_g_eq_gcd, ← an'_eq_w₀]
          norm_cast
          trans ↑(a n' * b n').natAbs
          norm_cast
          · apply Int.gcd_mul_lcm
          apply Int.natAbs_of_nonneg
          apply mul_nonneg
          all_goals linarith [h₀ n', h₁ n']
        rw [this]

        have : w₀ * (s n' - w₀) / g n' = w₀ * ((s n' - w₀) / g n') := by
          have : ↑(g n') ∣ (s n' - w₀) := by
            unfold g
            apply Int.dvd_sub
            exact Int.gcd_dvd_right
            exact Int.gcd_dvd_left
          obtain ⟨k, hk⟩ := this
          rw [hk]
          nth_rw 4 [mul_comm]
          rw [Int.mul_ediv_cancel]
          nth_rw 2 [mul_comm]
          rw [← mul_assoc, Int.mul_ediv_cancel]
          repeat norm_cast; exact g_nonzero n'
        rw [this]

        have : w₀.gcd ((g n') + w₀ * ((s n' - w₀) / (g n'))) = w₀.gcd (g n') := by
          unfold Int.gcd
          rw [Int.natAbs_add_of_nonneg, Int.natAbs_mul]
          apply Nat.gcd_add_mul_left_right
          exact Int.ofNat_zero_le (g n')
          apply mul_nonneg
          exact w_nonneg N
          apply Int.ediv_nonneg
          unfold s
          rw [← an'_eq_w₀]
          simp
          linarith [h₁ n']
          exact Int.ofNat_zero_le (g n')
        rw [this]

        -- then gcd(w₀, s n) = gcd(w₀, g n + (...) * w₀) = gcd(w₀, g n) = g n
        have : w₀.gcd (g n') = g n' := by
          have : ↑(g n') ∣ w₀ := by
            unfold g
            exact Int.gcd_dvd_left
          exact Int.gcd_eq_right this
        rw [this]

    have h_stable_g' := stable_of_eq_succ this
    unfold g' at h_stable_g'
    simp at h_stable_g'
    intro n n_ge_N
    rw [← h_stable_g' (n - N)]
    congr
    exact (Nat.sub_eq_iff_eq_add n_ge_N).mp rfl

  -- let g₀ := g N be the stable value
  let g₀ := g N

  -- we have w₀ > g₀
  have w₀_gt_g₀ : w₀ > g₀ := by
    unfold g₀ g
    apply lt_of_le_of_ne
    · apply Int.le_of_dvd
      exact w_pos N
      exact Int.gcd_dvd_left
    have : ¬ w₀ ∣ s N := w_mem_W N |>.2
    intro h_eq
    have : w₀ ∣ s N := by
      rw [← h_eq]
      exact Int.gcd_dvd_right
    contradiction

  -- let t := w₀ - g₀, this will be the period of a n
  let t := (w₀ - g₀).toNat

  -- we show the following inductive properties of a n for n ≥ N
  -- 1. if a n ≠ w₀, then a (n + 1) = a n + 1
  have an_succ_of_below : ∀ n ≥ N, a n ≠ w₀ → a (n + 1) = a n + 1 := by
    intro n n_ge_N h_ne
    have : a n < w₀ := by
      apply lt_of_le_of_ne
      exact an_le_w₀ n n_ge_N
      exact h_ne
    apply an_dvd_bn_of_lt_w₀ at this
    rw [lem_1_1 n |>.mp this]
    exact n_ge_N

  -- 2. if a n = w₀, then a (n + 1) = g₀ + 1
  have an_succ_of_eq : ∀ n ≥ N, a n = w₀ → a (n + 1) = g₀ + 1 := by
    intro n n_ge_N h_eq
    unfold g₀
    rw [h₃ n, ← h_g_stable_N n n_ge_N]
    have : Int.gcd (a n) (b n) = Int.gcd (a n) (s n) := by
      unfold s Int.gcd
      rw [Int.natAbs_add_of_nonneg]
      exact Eq.symm (Nat.gcd_self_add_right (a n).natAbs (b n).natAbs)
      all_goals linarith [h₀ n, h₁ n]
    rw [this, h_eq]

  -- this implies that if (a n) + d ≤ w₀, then a (n + d) = (a n) + d
  have an_add_of_le : ∀ n ≥ N, ∀ d : ℕ, a n + d ≤ w₀ → a (n + d) = a n + d := by
    intro n n_ge_N d h_le
    induction' d with d ih
    · simp
    rw [← add_assoc, an_succ_of_below, Nat.cast_add, ← add_assoc, Nat.cast_one]
    simp
    apply ih
    all_goals rw [Nat.cast_add, ← add_assoc, Nat.cast_one] at h_le;
    linarith
    linarith
    rw [ih]
    linarith
    linarith

  -- let N' := N + (w₀ - a N), we show that a n is periodic after N'
  let N' := N + (w₀ - a N).toNat

  use N', t
  simp
  constructor
  · unfold t
    simp [w₀_gt_g₀]

  -- first, we show a n is lower bound by g₀ + 1
  have a_n_ge_g₀_succ : ∀ n ≥ N', a n ≥ g₀ + 1 := by
    intro n hn
    induction n, hn using Nat.le_induction
    case base =>
      rw [an_add_of_le, Int.toNat_sub_of_le]
      linarith
      apply an_le_w₀ N
      rfl
      rfl
      rw [Int.toNat_sub_of_le]
      simp
      apply an_le_w₀ N
      rfl
    case succ n hn ih =>
      by_cases h : a n = w₀
      · rw [an_succ_of_eq]
        trans N'
        exact hn
        unfold N'
        linarith
        exact h
      · rw [an_succ_of_below]
        linarith
        trans N'
        exact hn
        unfold N'
        linarith
        exact h

  -- let n ≥ N' be arbitrary, our goal is a (n + t) = a n
  intro n n_ge_N'

  have n_ge_N : n ≥ N := by exact Nat.le_of_add_right_le n_ge_N'

  -- 1. a (n + w₀ - a n) = w₀
  let n₁ := n + (w₀ - a n).toNat
  have h_a_n₁_eq_w₀ : a n₁ = w₀ := by
    have : (w₀ - a n).toNat = w₀ - a n := by
        exact Int.toNat_sub_of_le (an_le_w₀ n n_ge_N)
    rw [an_add_of_le]
    · rw [this]
      ring
    exact n_ge_N
    rw [this]
    have : a n + (w₀ - a n) = w₀ := by
      exact add_sub_cancel (a n) w₀
    rw [this]

  -- 2. a (n + w₀ - a n + 1) = g₀ + 1
  let n₂ := n₁ + 1
  have h_a_n₂_eq_g₀_succ : a n₂ = g₀ + 1 := by
    apply an_succ_of_eq
    unfold n₁
    linarith
    exact h_a_n₁_eq_w₀

  -- we write t = (w₀ - a n + 1) + (a n - (g₀ + 1))
  have : t = (w₀ - a n).toNat + 1 + (a n - (g₀ + 1)) := by
    unfold t
    have : (w₀ - g₀).toNat = w₀ - g₀ := by
      apply Int.toNat_sub_of_le
      exact Int.le_of_lt w₀_gt_g₀
    rw [this]
    have : (w₀ - a n).toNat = w₀ - a n := by
      exact Int.toNat_sub_of_le (an_le_w₀ n n_ge_N)
    rw [this]
    ring
  have : t = ((w₀ - a n).toNat + 1 + (a n - (g₀ + 1))).toNat := by
    rw [← this]
    simp
  rw [this]

  have : (w₀ - a n).toNat = w₀ - a n := by
    exact Int.toNat_sub_of_le (an_le_w₀ n n_ge_N)
  rw [this]

  -- then we can show using the inductive properties of a n that:
  -- a (n + t) = a (n + (w₀ - a n + 1) + (a n - (g₀ + 1)))
  -- = a (n + w₀ - a n + 1) + (a n - (g₀ + 1))
  -- = g₀ + 1 + (a n - (g₀ + 1)) = a n
  unfold n₂ n₁ at h_a_n₂_eq_g₀_succ
  rw [Int.toNat_add, Int.toNat_add, Int.toNat_one, ← add_assoc, an_add_of_le, ← add_assoc, h_a_n₂_eq_g₀_succ]

  rw [Int.toNat_sub_of_le]
  ring

  exact a_n_ge_g₀_succ n n_ge_N'
  linarith
  · rw [← h_a_n₂_eq_g₀_succ]
    rw [Int.toNat_sub_of_le, ← add_assoc]
    linarith [an_le_w₀ n n_ge_N]
    rw [h_a_n₂_eq_g₀_succ]
    exact a_n_ge_g₀_succ n n_ge_N'
  · simp [an_le_w₀ n n_ge_N]
  · norm_num
  · linarith
  linarith [a_n_ge_g₀_succ n n_ge_N']
