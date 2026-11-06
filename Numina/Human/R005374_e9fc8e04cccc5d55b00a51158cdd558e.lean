import Mathlib

open Finset

/- Let $n$ be a natural number. Count the number of numbers $k \in\{0,1,2, \ldots, n\}$ such that $\binom{n}{k}$ is odd. Show that this number is a power of two, i.e. of the form $2^{p}$ for some natural number $p$. -/

noncomputable def sol := (fun n : ℕ => ((Iic n).filter (fun k ↦ Odd (n.choose k))).card)

theorem combinatorics_607963 {n : ℕ} : ∃ p, sol n = 2 ^ p := by

  -- Start with a simple fact using binary expansion.
  have binary (n : ℕ) : n ≠ 0 → ∃r, ∃m, n = 2^r + m ∧ m < 2^r := by
    intro
    induction' n with n ind
    · trivial
    · by_cases hn : n = 0
      · rw [hn]
        use 0, 0
        trivial
      · obtain ⟨r,m,h⟩ := ind hn
        by_cases hm : m + 1 < 2^r
        · use r, m+1
          rw [h.left]
          trivial
        · use r + 1, 0
          constructor
          repeat omega

  -- Key observation is the following.
  -- The fundamental property $\binom{n+1}{p}=\binom{n}{p-1}+\binom{n}{p}$ of the Pascal Triangle implies that if all numbers on line $k$ are $\equiv 1 \bmod 2$, then on line $k+1$ exactly the first and last numbers are $\equiv 1 \bmod 2$.
  -- If, say on line $k$ exactly the first and last numbers are $\equiv 1 \bmod 2$, then the lines $k, k+1, \ldots, 2 k-1$ are formed by two copies of lines $0,1, \ldots k-1$, separated by zeroes. As line 0 has number 1 and line 1 is formed by two ones, the lines 2 and three are formed by two copies of lines 0 and 1 , etc.
  -- By induction we infer that for every $k$, the line $2^{r}-1$ is forned of ones only - it has two copies of line $2^{r-1}-1$, and the line $0=2^{0}-1$ is a one.

  -- Concretely, we show all this by induction on n
  have lem : ∀ r, (∀ k < 2 ^ r, (2^r - 1).choose k % 2 = 1) ∧ (∀ m < 2^r, ∀k, (k ≤ m → (2^r + m).choose k % 2 = m.choose k % 2) ∧ (2^r ≤ k → k ≤ 2^r + m → (2^r + m).choose k % 2 = m.choose (k - 2^r) % 2) ∧ (m < k → k < 2^r → (2^r + m).choose k % 2 = 0)) := by
    intro r
    induction r
    case zero =>
      simp
      intro k
      constructor
      · intro hk
        simp [hk]
      constructor
      · intros
        have hk : k = 1 := by omega
        simp [hk]
      · intros
        linarith

    case succ r indr =>
      have oddline : ∀ k < 2 ^ (r + 1), (2 ^ (r + 1) - 1).choose k % 2 = 1 := by
        intro k _
        rw [(by omega : 2 ^ (r + 1) - 1 = 2^r + (2^r - 1))]
        by_cases hk : k < 2^r
        · rw [(indr.right (2^r - 1) (by omega) k).left]
          rw [indr.left]
          repeat omega
        · simp at hk
          rw [(indr.right (2^r - 1) (by omega) k).right.left]
          rw [indr.left]
          repeat omega
      constructor
      · exact oddline
      · intro m
        induction m
        case zero =>
          simp
          intro k
          constructor
          · intro hk
            simp [hk]
          constructor
          · intro _ _
            have hk : k = 2^(r+1) := by linarith
            simp [hk]
          · intro _ _
            rw [Nat.choose_eq_choose_pred_add]
            rw [Nat.add_mod]
            rw [oddline k, oddline (k-1)]
            repeat omega
        case succ m indm =>
          intro hm
          replace indm := indm <| (Nat.lt_succ_self _).trans hm
          intro k
          constructor
          · intros
            -- The boundary case $k = 0$ is immediate
            by_cases hk : k = 0
            · simp [hk]
            rw [Nat.choose_succ_left, Nat.add_mod]
            rw [(by ring : 2^(r + 1) + (m + 1) = 2^(r + 1) + m + 1), Nat.choose_succ_left, Nat.add_mod]
            congr 2
            refine (indm (k-1)).left ?_
            repeat omega
            -- The boundary case $k = m + 1$ needs to be treated separately
            by_cases hk : k = m + 1
            · simp [hk]
              refine (indm (m+1)).right.right ?_ ?_
              repeat omega
            -- For $k$ in the interior segment, apply inductive hypothesis
            refine (indm k).left ?_
            repeat omega
          constructor
          · intros
            -- The boundary case $k = 2 ^ (r + 1)$ needs to be treated separately
            by_cases hk : k = 2 ^ (r + 1)
            · simp [hk]
              rw [(by omega : 2^(r + 1) + (m + 1) = 2^(r + 1) + m + 1), Nat.choose_succ_left, Nat.add_mod]
              rw [(indm (2^(r+1))).right.left]
              rw [(indm _).right.right]
              simp
              repeat omega
            -- Boundary case $k = $ ^ (r + 1) + m + 1$ is easy
            by_cases hk : k = 2 ^ (r + 1) + m + 1
            · rw [hk]
              congr 1
              rw [(by omega : 2 ^ (r + 1) + m + 1 - 2 ^ (r + 1) = m + 1)]
              simp only [Nat.choose_self]
              apply Nat.choose_self
            -- For $k$ in the interior segment, apply inductive hypothesis
            rw [Nat.choose_succ_left, Nat.add_mod]
            rw [(by ring : 2^(r + 1) + (m + 1) = 2^(r + 1) + m + 1), Nat.choose_succ_left, Nat.add_mod]
            congr 2
            rw [(indm (k-1)).right.left]
            congr 2
            repeat omega
            refine (indm k).right.left ?_ ?_
            repeat omega
          · intros
            rw [(by ring : 2^(r + 1) + (m + 1) = 2^(r + 1) + m + 1), Nat.choose_succ_left, Nat.add_mod]
            convert Nat.zero_mod 2
            convert Nat.zero_add 0 <;>
            refine (indm ?_).right.right ?_ ?_
            repeat omega

  -- We only need a part of the lemma
  -- replace lem := fun r => (lem r).right

  induction' n using Nat.strong_induction_on with n indn

    -- The case $n = 0$ is trivial
  by_cases hn' : n = 0
  · use 0
    simp [sol, hn']
    trivial

  · -- Otherwise, write $n = 2^r + m$ with $m < 2^r$
    obtain ⟨r,m,hnrm,hrm⟩ := binary n hn'

    -- Use the second part of the lemma and induction.
    replace lem := ((lem r).right m) hrm

    -- The n-th line consists of two copies (MOD 2) of the m-th line padded with even numbers in the middle.
    -- So we use the induction hypothesis for $m$.
    -- We have double the number of odd numbers at line $n = 2^r + m$ compared to at line $m$
    obtain ⟨p,hp⟩ := indn m (by linarith)
    use p + 1
    simp [sol]

    -- For the sake of rigor, write interval $\{0, \dotsc, n\}$ as a dijoint union of three subintervals
    have Dj : Disjoint (Iic m) (Ioo m (2^r)) := by
      rw [disjoint_iff_inter_eq_empty]
      rw [← subset_empty]
      intro x hx
      simp at hx
      linarith
    have dU : Iio (2^r) = (Iic m).disjUnion (Ioo m (2^r)) Dj := by
      simp
      rwa [← Finset.coe_inj, Finset.coe_union, Finset.coe_Iio, Finset.coe_Iic, Finset.coe_Ioo, Set.Iic_union_Ioo_eq_Iio]

    have Dj' : Disjoint (Iio (2^r)) (Icc (2^r) n) := by
      rw [disjoint_iff_inter_eq_empty]
      rw [← subset_empty]
      intro x hx
      simp at hx
      linarith
    have dU' : Iic n = (Iio (2^r)).disjUnion (Icc (2^r) n) Dj' := by
      simp
      rw [← Finset.coe_inj, Finset.coe_union, Finset.coe_Iio, Finset.coe_Iic, Finset.coe_Icc, Set.Iio_union_Icc_eq_Iic]
      linarith

    rw [dU', filter_disj_union, card_disjUnion]
    rw [dU, filter_disj_union, card_disjUnion]

    -- Now use the lemma.
    suffices #(filter (fun k ↦ Odd (n.choose k)) (Iic m)) = 2 ^ p ∧ #(filter (fun k ↦ Odd (n.choose k)) (Ioo m (2 ^ r))) = 0 ∧ #(filter (fun k ↦ Odd (n.choose k)) (Icc (2 ^ r) n)) = 2 ^ p by omega

    constructor
    · simp_rw [← hp, sol, Nat.odd_iff, hnrm]
      apply card_bijective id Function.bijective_id
      simp
      intro k _
      rw [(lem k).left (by linarith)]
    constructor
    · rw [card_filter_eq_zero_iff]
      simp [hnrm, Nat.even_iff]
      intro k _ _
      apply (lem k).right.right
      repeat assumption
    · simp_rw [← hp, sol, Nat.odd_iff, hnrm]
      apply Eq.symm
      refine card_nbij (fun k => 2^r + k) ?_ ?_ ?_
      · simp
        intro k hk hok
        constructor
        assumption
        rw [(lem (2^r + k)).right.left (by linarith) (by linarith)]
        simpa
      · apply Set.injOn_of_injective
        intro _ _
        simp
      · intro k
        simp
        intro _ _ _
        use k - 2 ^ r
        repeat constructor
        omega
        rwa [← (lem k).right.left]
        repeat omega