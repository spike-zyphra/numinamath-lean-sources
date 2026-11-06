import Mathlib
set_option maxHeartbeats 0

/-Find all positive integers $n$ with the following property: the $k$ positive divisors of $n$ have a permutation $\left(d_{1}, d_{2}, \ldots, d_{k}\right)$ such that for every $i=1,2, \ldots, k$, the number $d_{1}+\cdots+d_{i}$ is a perfect square.-/
theorem number_theory_24211 {n : ℕ} {npos : 0 < n} : (∃ d s : ℕ → ℕ,
Set.BijOn d (Finset.range (n.divisors.card)) n.divisors ∧
∀ i ∈ Finset.range (n.divisors.card), ∑ j ∈ Finset.range (i + 1), d j = (s i) ^ 2) ↔
(n = 1 ∨ n = 3) := by
-- Prove the following lemma computing the sum of all odd numbers from $1$ to $2n-1$
  have lm : ∀ n, ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
    intro n'; rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_id]
    simp; rw [mul_comm, Nat.div_mul_cancel, Nat.mul_sub, mul_one]
    rw [Nat.sub_add_cancel]; ring
    exact Nat.le_mul_self n'
    rw [← Nat.div_add_mod n' 2]; have : n' % 2 < 2 := by apply Nat.mod_lt; simp
    interval_cases n' % 2; any_goals simp_all
    · rw [mul_assoc]; simp
    rw [mul_comm, mul_assoc]; simp
  constructor
-- To prove the "if" part of the goal, we first introduce the variables and assumptions in question
  · rintro ⟨d, s, h⟩; rcases h with ⟨perm, sumsq⟩
  -- Prove that $1$ is a divisor of $n$
    have onedn : 1 ∈ n.divisors := by rw [Nat.mem_divisors]; simp; linarith
  -- Prove that $d_i$ divides $n$ for all $i$ in Finset.range n.divisors.card
    have ddvdn : ∀ i ∈ Finset.range n.divisors.card, d i ∣ n := by
      intro i hi; suffices : d i ∈ n.divisors
      · rw [Nat.mem_divisors] at this; exact this.left
      apply perm.mapsTo; exact hi
  -- Prove that $d_i$ is positive for all $i$ in Finset.range n.divisors.card
    have dpos : ∀ i ∈ Finset.range n.divisors.card, 0 < d i := by
      intro i hi; suffices : d i ∈ n.divisors
      · rw [Nat.mem_divisors] at this; rcases this with ⟨h,_⟩
        exact Nat.pos_of_dvd_of_pos h npos
      apply perm.mapsTo; exact hi
  -- Prove that $s_i$ is positive for all $i$ in Finset.range n.divisors.card
    have spos : ∀ i ∈ Finset.range n.divisors.card, 0 < s i := by
      intro i hi; by_contra h; simp at h
      have := sumsq i hi; rw [Finset.sum_range_succ, h, zero_pow] at this
      have := dpos i hi; have : 0 ≤ ∑ x ∈ Finset.range i, d x := by simp
      linarith; norm_num
  -- Prove that $s$ is strictly increasing
    have smono : StrictMonoOn s (Finset.range n.divisors.card) := by
      intro i hi j; induction j; simp
      rename_i j ih; intro hj1 hj2
      have : s j < s (j + 1) := by
        have tmph1 := sumsq j (show _ by simp; simp at hj1; linarith)
        have tmph2 := sumsq (j+1) hj1
        rw [Finset.sum_range_succ, tmph1] at tmph2
        suffices : s j ^ 2 < (s (j + 1)) ^ 2
        · rw [Nat.pow_lt_pow_iff_left] at this
          assumption; norm_num
        have := dpos (j+1) hj1; linarith
      replace ih := ih (show _ by simp; simp at hj1; linarith)
      by_cases h : i < j
      · replace ih := ih h; linarith
      replace h : i = j := by linarith
      rw [h]; assumption
  -- Prove that $d_0$ is $1$
    have d0 : d 0 = 1 := by
      obtain ⟨i, ⟨hi1, hi2⟩⟩ : ∃ i ∈ Finset.range (n.divisors.card), d i = 1 := by
        apply perm.surjOn at onedn; assumption
      have tmph1 := sumsq i hi1; rw [Finset.sum_range_succ] at tmph1
      by_cases h : i < 1
      · simp at h; rw [h] at hi2; assumption
      push_neg at h; simp at hi1
      have aux1 : i - 1 < i := Nat.sub_one_lt_of_lt h
      have aux2 : s (i - 1) < s i := by apply smono; any_goals simp; linarith
      have tmph2 := sumsq (i-1) (show _ by simp; apply lt_trans _ hi1; assumption)
      rw [Nat.sub_add_cancel] at tmph2; rw [tmph2] at tmph1
      apply Nat.eq_sub_of_add_eq' at tmph1; rw [Nat.sq_sub_sq, hi2] at tmph1
      symm at tmph1; simp at tmph1; suffices : s (i - 1) = 0
      · have := spos (i-1) (show _ by simp; apply lt_trans _ hi1; assumption)
        linarith
      any_goals linarith
  -- Prove that $s_0$ is $1$
    have s0 : s 0 = 1 := by
      specialize sumsq 0; replace sumsq := sumsq (show _ by simp; linarith)
      simp at sumsq; rw [d0, show 1 = 1^2 by simp] at sumsq
      apply Nat.pow_left_injective at sumsq; symm at sumsq
      assumption; norm_num
  -- The following key proposition comes from the reference answer, it gives an explicit formula for all $d_i$. We will prove it by using strong induction
    have key : ∀ i ∈ Finset.range (n.divisors.card), d i = 2 * i + 1 := by
      intro i; induction i using Nat.strong_induction_on
      rename_i i ih; by_cases h : i < 1; simp at h
    -- Prove the base case when $i$ is $0$
      · intro; simp [h]; assumption
      push_neg at h; intro h'
      have aux1 : i - 1 < i := Nat.sub_one_lt_of_lt h
    -- Specialize the hypothesis sumsq to $i$ and $i-1$, then rewrite them
      have sumi := sumsq i h'
      have sumis1 := sumsq (i-1) (show _ by simp; simp at h'; linarith)
      rw [Nat.sub_add_cancel] at sumis1
      rw [Finset.sum_range_succ, sumis1] at sumi; apply Nat.eq_sub_of_add_eq' at sumi
      rw [Nat.sq_sub_sq] at sumi
    -- Apply the induction hypothesis ih to $i$
      have ihi : ∀ j ∈ Finset.range i, d j = 2 * j + 1 := by
        intros; apply ih; any_goals simp_all
        linarith
    -- Rewrite the sum in sumis1 and apply lemma lm
      rw [Finset.sum_congr rfl ihi, lm] at sumis1
      apply Nat.pow_left_injective (show 2≠0 by simp) at sumis1; symm at sumis1
      rw [sumis1] at sumi
    -- From the product in sumi, we see that $s_i+i$ is a divisor of $n$, therefore we can apply perm to find a $j$ such that $d_j$ equals $s_i+i$
      obtain ⟨j, ⟨hj1, hj2⟩⟩ : ∃ j ∈ Finset.range n.divisors.card, d j = s i + i := by
        suffices : s i + i ∈ n.divisors
        · apply perm.surjOn this
        rw [Nat.mem_divisors]; constructor; any_goals linarith
        · apply Nat.dvd_trans _ (ddvdn i h'); use s i - i
    -- Prove that $j$ is positive
      have jpos : 0 < j := by
        by_contra!; simp_all
        have := dpos i (show _ by linarith); linarith
      have aux2 : j - 1 < j := Nat.sub_one_lt_of_lt jpos
    -- Specialize the assumption sumsq to $j$ and $j-1$, then rewrite them
      have sumj := sumsq j hj1; rw [Finset.sum_range_succ] at sumj
      have sumjs1 := sumsq (j-1) (show _ by simp; simp at hj1; linarith)
      rw [Nat.sub_add_cancel] at sumjs1; rw [sumjs1] at sumj
      apply Nat.eq_sub_of_add_eq' at sumj; rw [Nat.sq_sub_sq] at sumj
      replace sumj : s j + s (j - 1) ≤ d j := by
        rw [sumj]; nth_rw 1 [← mul_one (s j + s (j - 1))]
        rw [mul_le_mul_left]; by_contra!; simp at this
        simp [this] at sumj; have := dpos j hj1; linarith
        apply add_pos; any_goals apply spos
        · exact hj1
        simp; simp at hj1; linarith
    -- Assuming that $j$ is equal to $i$, we can prove the final goal
      suffices : j = i
      · rw [this] at hj2; symm at hj2; apply Nat.eq_sub_of_add_eq at hj2
        rw [hj2, Nat.sub_add_cancel] at sumi; nth_rw 1 [← mul_one (d i)] at sumi
        rw [Nat.mul_right_inj] at sumi; rw [sumi]
        zify; repeat rw [Nat.cast_sub]
        ring
        any_goals have := spos i h'; apply le_of_lt; rw [← Nat.sub_pos_iff_lt]; linarith
        have := dpos i h'; linarith
    -- To prove that $j=i$, we prove by contradiction and split the goal to two cases : $i$ less than $j$ and $j$ less than $i$
      by_contra!; rw [ne_iff_lt_or_gt] at this; rcases this with h''|h''
      · specialize ihi j; replace ihi := ihi (show _ by simp; assumption)
        rw [ihi] at hj2; apply smono at aux1; linarith
        simp; simp at h'; linarith
        exact h'
      rw [gt_iff_lt] at h''; have := smono h' hj1 h''
      have := smono (show i-1 ∈ Finset.range n.divisors.card by simp; simp at h'; linarith) (show j-1 ∈ Finset.range n.divisors.card by simp; simp at hj1; linarith)
      replace this := this (show _ by rw [Nat.sub_lt_sub_iff_right]; assumption; linarith)
      linarith; any_goals linarith
  -- Split the final goal to two cases when $n$ is even or odd
    rcases Nat.even_or_odd' n with ⟨k, hk|hk⟩
    · suffices : 2 ∈ n.divisors
    -- It is impossible to have $n$ even because the key lemma says all divisors of $n$ are odd
      · apply perm.surjOn at this; rcases this with ⟨i, ⟨hi1, hi2⟩⟩
        rw [key] at hi2; have := Nat.not_even_two_mul_add_one i
        rw [hi2] at this; contradiction; assumption
      rw [Nat.mem_divisors]; constructor; use k; linarith
  -- If $n$ is odd, let $n=2k+1$. If $k$ is less than $2$, then we immediately have $n$ equals $1$ or $3$
    by_cases h : k < 2
    · interval_cases k; any_goals simp_all
  -- If $k$ is greater or equal to $2$, we prove that $n-2$ has to divide $2$, which is impossible by linear arithmetic
    push_neg at h
    obtain ⟨j, ⟨hj1, hj2⟩⟩ : ∃ j ∈ Finset.range n.divisors.card, d j = n := by
      suffices : n ∈ n.divisors
      · apply perm.surjOn this
      simp; linarith
    simp at hj1; rw [hk, key] at hj2; replace hj2 : j = k := by linarith
    have : j - 1 < j := by apply Nat.sub_one_lt; linarith
    suffices : n - 2 ∣ 2
    · apply Nat.le_of_dvd at this; rw [Nat.sub_le_iff_le_add] at this
      any_goals linarith
    nth_rw 2 [show 2 = n - (n - 2) by rw [Nat.sub_sub_eq_min, Nat.min_eq_right]; any_goals linarith]
    apply Nat.dvd_sub; exact Nat.sub_le n 2
    suffices : n - 2 ∈ n.divisors
    · rw [Nat.mem_divisors] at this; exact this.left
    suffices : d (j - 1) = n - 2
    · rw [← this]; apply perm.mapsTo; simp; linarith
    rw [key]; zify; repeat rw [Nat.cast_sub]
    rw [hk, hj2]; push_cast; ring
    any_goals linarith
    any_goals simp; linarith
    rfl
-- Conversely, if $n$ is $1$ or $3$, it is easy to construct the desired functions in question since $1$ and $3$ have only a few divisors
  intro h; rcases h with h|h
-- If $n$ equals $1$, then we let $d$ and $s$ to be the constant function at $1$
  · simp [h]; let d : ℕ → ℕ := fun t => 1; let s : ℕ → ℕ := fun t => 1
    use d; simp; use s; simp [d, s]
  rw [h, show Nat.divisors 3 = {1,3} by decide]
-- If $n$ equals $3$, we let $d_0$ to be $1$ and $3$ otherwise, let $s_0$ to be $1$ and $2$ otherwise
  let d : ℕ → ℕ := fun t => if t = 0 then 1 else 3
  let s : ℕ → ℕ := fun t => if t = 0 then 1 else 2
  use d; use s; constructor
-- Prove that $d$ is bijective on the required subset
  · simp; rw [Set.BijOn]; split_ands
    · rw [Set.MapsTo]; intro i hi; simp at hi
      simp [d]; exact Or.symm (ne_or_eq i 0)
    · intro i hi j hj; simp [d]; split_ifs; any_goals simp_all
      replace hi : i = 1 := by
        suffices : 0 < i; linarith
        rw [← Nat.ne_zero_iff_zero_lt]; assumption
      replace hj : j = 1 := by
        suffices : 0 < j; linarith
        rw [← Nat.ne_zero_iff_zero_lt]; assumption
      linarith
    rw [Set.SurjOn, Set.subset_def]; intro i hi; simp at hi
    simp [d]; rcases hi with hi|hi
    · use 0; simp; symm; exact hi
    use 1; simp; symm; exact hi
-- Prove that the sum of all $d_i$'s equals the square of $s_i$
  intro i hi; simp at hi; interval_cases i; any_goals simp_all
  · simp [d, s]
  simp [d, s]; rw [Finset.range_succ, Finset.sum_insert]; any_goals simp