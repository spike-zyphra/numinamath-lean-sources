import Mathlib
set_option maxHeartbeats 0

/-Given a positive integer $n$, find the smallest value of $\left\lfloor\frac{a_{1}}{1}\right\rfloor+\left\lfloor\frac{a_{2}}{2}\right\rfloor+\cdots+\left\lfloor\frac{a_{n}}{n}\right\rfloor$ over all permutations $\left(a_{1}, a_{2}, \ldots, a_{n}\right)$ of $(1,2, \ldots, n)$.-/
theorem algebra_24128 (n : ℕ) (npos : 0 < n) : IsLeast {m : ℕ | ∃ a : ℕ → ℕ,
Set.BijOn a (Finset.range n) (Finset.range n) ∧
m = ∑ i ∈ Finset.range n, (a i + 1) / (i + 1)} (Nat.log 2 n + 1) := by
-- Prove a simple inequality about $Nat.log 2 n$, then rewrite assumptions and goals
  have powlogn : 2 ^ (Nat.log 2 n) ≤ n := by apply Nat.pow_log_le_self; linarith
  rw [IsLeast, lowerBounds]; simp; constructor
  -- Define the following function $a$ according to the reference answer and prove it satisfies the desired properties
  · let a : ℕ → ℕ := fun i => if i = 2 ^ (Nat.log 2 i + 1) - 1 then (if 2 * i < n then 2 * i else n - 1) else i - 1
    use a; constructor; rw [Set.BijOn]; split_ands
  -- Prove $a$ maps Finset.range $n$ to Finset.range $n$
    · intro i; simp [a]; intro hi; split_ifs
      assumption; exact Nat.sub_one_lt_of_lt npos
      exact tsub_lt_of_lt hi
  -- Prove $a$ is injective on Finset.range $n$
    · intro i hi j hj hij; simp [a] at hij
      simp at hi hj; split_ifs at hij
    -- Split the goal to eight cases according to the definition of $a$ and prove them case by case
    -- In the first case, we can cancel the multiplication by $2$ at hypothesis hij to show $i=j$
      · apply Nat.mul_left_cancel (show 0<2 by simp); exact hij
    -- In the second case, we rewrite the assumptions by applying properties of powers and use linarith to find a contradiction
      · rename_i hi1 hi2 hj1 hj2; push_neg at hj2
        rw [← add_left_inj 1, Nat.sub_add_cancel] at hij
        rw [← hij, hi1, hj1, Nat.mul_sub] at hj; nth_rw 2 [two_mul] at hj
        rw [← pow_succ', ← Nat.sub_sub, Nat.sub_add_cancel, Nat.sub_lt_sub_iff_right] at hj
        rw [Nat.pow_lt_pow_iff_right, Nat.lt_add_one_iff, ← Nat.pow_le_pow_iff_right (show 1<2 by simp)] at hj
        rw [← add_left_inj 1, Nat.sub_add_cancel] at hi1 hj1
        rw [← hi1, ← hj1] at hj; any_goals linarith
        any_goals apply Nat.one_le_pow'
        rw [Nat.le_sub_iff_add_le, show 1+1 = 2^1 by simp, Nat.pow_le_pow_iff_right]; any_goals simp
        apply Nat.one_le_pow'
      -- In the third case, we rewrite the assumptions by applying properties of log function and power function,
      -- then we can prove that $j$ is equal to $2 ^ (Nat.log 2 j + 1) - 1$, contradicting to the hypothesis hj2
      · rename_i hi1 hj1 hj2; push_neg at hj2
        have : 1 ≤ j := by by_contra!; simp at this hij; simp [this] at hij; simp [hij] at hi1
        suffices : Nat.log 2 i + 1 = Nat.log 2 j
        · rw [← add_left_inj 1, Nat.sub_add_cancel, hi1, Nat.mul_sub] at hij
          nth_rw 2 [two_mul] at hij; rw [← pow_succ', ← Nat.sub_sub, Nat.sub_add_cancel] at hij
          rw [this] at hij; symm at hij; contradiction
          rw [Nat.le_sub_iff_add_le, show 1+1 = 2^1 by simp, Nat.pow_le_pow_iff_right]; any_goals simp
          apply Nat.one_le_pow'; assumption
        symm; rw [Nat.log_eq_iff]; rw [← add_left_inj 1, Nat.sub_add_cancel] at hij hi1
        rw [← hij, ← hi1, pow_succ, ← hi1]; constructor; any_goals linarith
        apply Nat.one_le_pow'; right; simp; linarith
      -- In the fourth case, we rewrite the assumptions by applying properties of powers and use linarith to find a contradiction
      · rename_i hi1 hi2 hj1 hj2; push_neg at hi2
        rw [← add_left_inj 1, Nat.sub_add_cancel] at hij
        rw [hij, hj1, hi1, Nat.mul_sub] at hi; nth_rw 2 [two_mul] at hi
        rw [← pow_succ', ← Nat.sub_sub, Nat.sub_add_cancel, Nat.sub_lt_sub_iff_right] at hi
        rw [Nat.pow_lt_pow_iff_right, Nat.lt_add_one_iff, ← Nat.pow_le_pow_iff_right (show 1<2 by simp)] at hi
        rw [← add_left_inj 1, Nat.sub_add_cancel] at hi1 hj1
        rw [← hi1, ← hj1] at hi; linarith
        any_goals apply Nat.one_le_pow'
        any_goals linarith
        rw [Nat.le_sub_iff_add_le, show 1+1 = 2^1 by simp, Nat.pow_le_pow_iff_right]; any_goals simp
        apply Nat.one_le_pow'
      -- In the fifth case, we apply various properties of log function and power function to prove $i$ equals $j$
      · rename_i hi1 hi2 hj1 hj2; push_neg at hi2 hj2; by_cases h : n < 2
        · replace h : n = 1 := by linarith
          simp [h] at *; linarith
        push_neg at h
        suffices tmph1 : ∀ k, k < n → k = 2 ^ (Nat.log 2 k + 1) - 1 → n ≤ 2 * k → Nat.log 2 k = Nat.log 2 n - 1
        · have logi := tmph1 i hi hi1 hi2; have logj := tmph1 j hj hj1 hj2
          rw [hi1, hj1, logi, logj]
        intro k hk1 hk2 hk3; rw [Nat.log_eq_iff]; constructor
        · rw [← mul_le_mul_left (show 0<2 by simp), ← pow_succ', Nat.sub_add_cancel]
          apply le_trans _ hk3; exact powlogn
          apply Nat.le_log_of_pow_le; any_goals linarith
        rw [Nat.sub_add_cancel, Nat.lt_iff_add_one_le]
        rw [← add_left_inj 1, Nat.sub_add_cancel] at hk2
        rw [hk2, Nat.pow_le_pow_iff_right]; rw [Nat.lt_iff_add_one_le, hk2] at hk1
        apply Nat.le_log_of_pow_le; any_goals linarith
        exact Nat.one_le_two_pow
        apply Nat.le_log_of_pow_le; any_goals linarith
        right; simp; linarith
      -- In the sixth case, we rewrite the assumptions and simplify them to $n=1$, then we can easily find a contradiction
      · rename_i hi1 hi2 hj1; symm at hij; rw [Nat.sub_eq_iff_eq_add, Nat.sub_add_cancel] at hij; any_goals linarith
        by_contra!; simp at this; simp [this] at hij
        replace hij : n = 1 := by symm at hij; rw [Nat.sub_eq_zero_iff_le] at hij; linarith
        simp [hij] at hi; simp [hi] at hi1
      -- In the seventh case, we rewrite the assumptions by applying properties of log function and power function,
      -- then we can prove that $i$ is equal to $2 ^ (Nat.log 2 i + 1) - 1$, contradicting to the hypothesis hj2
      · rename_i hi1 hj1 hj2; push_neg at hi1
        have : 1 ≤ i := by by_contra!; simp at this hij; simp [this] at hij; simp [hij] at hj1
        suffices : Nat.log 2 j + 1 = Nat.log 2 i
        · rw [← add_left_inj 1, Nat.sub_add_cancel, hj1, Nat.mul_sub] at hij
          nth_rw 2 [two_mul] at hij; rw [← pow_succ', ← Nat.sub_sub, Nat.sub_add_cancel] at hij
          rw [this] at hij; contradiction
          rw [Nat.le_sub_iff_add_le, show 1+1 = 2^1 by simp, Nat.pow_le_pow_iff_right]; any_goals simp
          apply Nat.one_le_pow'; assumption
        symm; rw [Nat.log_eq_iff]; rw [← add_left_inj 1, Nat.sub_add_cancel] at hij hj1
        rw [hij, ← hj1, pow_succ, ← hj1]; constructor; any_goals linarith
        apply Nat.one_le_pow'; right; simp; linarith
      -- In the eighth case, we can prove that $i=n$ which contradicts to the fact that $i$ is less than $n$
      · rename_i hi1 hj1 hj2; symm at hij; rw [Nat.sub_eq_iff_eq_add, Nat.sub_add_cancel] at hij; any_goals linarith
        by_contra!; simp at this; simp [this] at hij
        simp [hij] at hi; simp [hij] at hj; simp [hj] at hj1
      -- In the last case, it is straightforward to get $i=j$ from the hypothese hij: $i-1=j-1$
      rename_i hi1 hj1; by_cases h : i < 1
      · simp at h; simp [h] at hij; symm at hij; rw [Nat.sub_eq_zero_iff_le] at hij
        interval_cases j; linarith; simp at hj1
      push_neg at h; rw [← add_left_inj 1, Nat.sub_add_cancel, Nat.sub_add_cancel] at hij; exact hij
      by_contra!; simp at this; simp [this] at hij; simp [hij] at hi1
      assumption
  -- Prove that $a$ is surjective, we proceed by splitting to various cases. The first case is when $i$ is zero
    intro i; simp [a]; intro hi; by_cases hi0 : i = 0
    · use 0; simp; constructor; any_goals linarith
  -- The seconde case is when $i$ is $n-1$, we prove that $a_(2^(Nat.log 2 n)-1)$ equals $n-1$
    push_neg at hi0; by_cases hi1 : i = n - 1
    · use 2 ^ (Nat.log 2 n) - 1; constructor
    -- Prove that $2^(Nat.log 2 n)-1$ is less than $n$
      · rw [Nat.lt_iff_add_one_le, Nat.sub_add_cancel]
        exact powlogn; apply Nat.one_le_pow'
    -- Split the goal to three cases according to the definition of $a$ and prove them case by case
      split_ifs
      -- In the first case, rewrite the definition of log function by Nat.log_eq_iff, then prove that $n = 2 * 2 ^ Nat.log 2 n - 1$
      · rename_i hi2 hi3
        have tmph1 : Nat.log 2 n = Nat.log 2 n := rfl
        rw [Nat.log_eq_iff, pow_succ'] at tmph1; rw [Nat.mul_sub, mul_one] at hi3
        have tmph2 : n = 2 * 2 ^ Nat.log 2 n - 1 := by
          rw [Nat.eq_iff_le_and_ge]; constructor
          · rw [Nat.le_sub_one_iff_lt]; exact tmph1.right
            positivity
          rw [Nat.lt_iff_add_one_le] at hi3; nth_rw 4 [show 2 = 1+1 by simp] at hi3
          rw [← Nat.sub_sub, Nat.sub_add_cancel] at hi3; exact hi3
          rw [Nat.le_sub_iff_add_le, show 1+1 = 2*1 by simp]; apply mul_le_mul
          rfl; apply Nat.one_le_pow'; any_goals simp
          rw [show 1 = 1*1 by simp]; apply mul_le_mul; simp; apply Nat.one_le_pow'
          any_goals simp
        rw [tmph2, Nat.sub_sub, show 1+1 = 2 by simp] at hi1
        rw [Nat.mul_sub, mul_one]; symm; exact hi1
        right; simp; linarith
      -- The second case is trivially given by hypothesis hi1
      · symm; exact hi1
    -- In the last case, we will prove that $Nat.log 2 n$ is equal to $Nat.log 2 (2 ^ Nat.log 2 n - 1) + 1$,
    -- and prove that this contradicts to the hypothese hi2
      rename_i hi2; push_neg at hi2
      have aux : 2 ^ Nat.log 2 n - 1 ≠ 0 := by
        intro h; replace h : n = 1 := by
          suffices : Nat.log 2 n = 0
          · rw [Nat.log_eq_zero_iff] at this; simp at this; linarith
          rw [Nat.sub_eq_zero_iff_le] at h
          replace h : 2 ^ Nat.log 2 n = 1 := by
            have := Nat.one_le_pow' (Nat.log 2 n) 1
            simp at this; linarith
          rw [show 1 = 2^0 by simp, pow_right_inj] at h; exact h; any_goals linarith
        simp [h] at hi1; contradiction
      suffices : 2 ^ Nat.log 2 n - 1 = 2 ^ (Nat.log 2 (2 ^ Nat.log 2 n - 1) + 1) - 1; contradiction
    -- Use Nat.log_eq_iff to rewrite the goal as two inequalities of power functions
      congr; rw [Nat.log_eq_iff]; constructor
      · rw [Nat.pow_le_iff_le_log, Nat.add_one_le_iff]
        apply Nat.log_lt_of_lt_pow; exact aux
        apply Nat.sub_one_lt; positivity; any_goals linarith
      rw [Nat.lt_pow_iff_log_lt, Nat.lt_add_one_iff, ← Nat.log_mul_base]; apply Nat.log_monotone
      rw [Nat.sub_mul, show 1*2 = 1+1 by simp, ← pow_succ, ← Nat.sub_sub]
      have tmph1 : Nat.log 2 n = Nat.log 2 n := rfl
      rw [Nat.log_eq_iff] at tmph1; by_contra tmph2; push_neg at tmph2
      replace tmph2 : n = 2 ^ (Nat.log 2 n + 1) - 1 := by
        rw [Nat.lt_iff_add_one_le, Nat.sub_add_cancel] at tmph2
        rw [Nat.eq_iff_le_and_ge]; constructor
        · rw [Nat.le_sub_iff_add_le, ← Nat.lt_iff_add_one_le]
          exact tmph1.right; apply Nat.one_le_pow'
        exact tmph2; rw [Nat.le_sub_iff_add_le, show 1+1 = 2^1 by simp]
        apply Nat.pow_le_pow_right; any_goals linarith
      have nge1 : 1 ≤ n := by
        rw [tmph2, Nat.le_sub_iff_add_le, show 1+1 = 2^1 by simp]
        apply Nat.pow_le_pow_right; any_goals linarith
      rw [← Nat.log_mul_base, Nat.sub_mul, ← pow_succ, show 1*2 = 1+1 by simp] at hi2
      rw [← Nat.sub_sub, ← tmph2] at hi2
      suffices : Nat.log 2 (n - 1) = Nat.log 2 n
      · simp [this] at hi2
      rw [Nat.log_eq_iff]; constructor
      · rw [Nat.le_sub_iff_add_le, Nat.add_one_le_iff, lt_iff_le_and_ne]
        constructor; exact powlogn
        by_contra!; nth_rw 2 [tmph2] at this
        rw [← add_left_inj 1, Nat.sub_add_cancel, pow_succ, mul_two] at this
        simp at this; rw [show 1 = 2^0 by simp, pow_right_inj] at this
        symm at this; rw [Nat.log_eq_zero_iff] at this; simp at this
        replace this : n = 1 := by linarith
        simp [this] at hi1; contradiction; any_goals linarith
      linarith; right; simp; intro h; rw [Nat.sub_eq_zero_iff_le] at h
      replace h : n = 1 := by linarith
      simp [h] at hi1; contradiction; any_goals linarith
      any_goals exact aux
      any_goals right; simp; linarith
  -- If $i$ is not $0$ or $n-1$, assume it is of the form $2^j-2$, prove that $a_(2^(j-1)-1)$ equals $i$
    push_neg at hi1; by_cases h2pow : ∃ j, i = 2 ^ j - 2
    · rcases h2pow with ⟨j, hj⟩
      have jge2 : 2 ≤ j := by
        by_contra!; interval_cases j
        any_goals simp at hj; contradiction
      use 2 ^ (j - 1) - 1; constructor
      · suffices : 2 ^ (j - 1) - 1 + (2 ^ (j - 1) - 1) < n; linarith
        rw [← two_mul, Nat.mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel]
        any_goals linarith
    -- Split the goal to three cases according to the definition of $a$ and prove them case by case
      split_ifs
      · rw [Nat.mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel]
        any_goals linarith
      · rename_i hj1; rw [Nat.mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel] at hj1
        rw [hj] at hi; contradiction; linarith
      rename_i hj1; suffices : 2 ^ (j - 1) - 1 = 2 ^ (Nat.log 2 (2 ^ (j - 1) - 1) + 1) - 1; contradiction
      congr; rw [← Nat.log_mul_base, mul_comm, Nat.mul_sub, mul_one]
      symm; rw [Nat.log_eq_iff]; constructor
      · rw [two_mul, Nat.add_sub_assoc]; simp
        nth_rw 1 [show 2 = 2^1 by simp]; apply Nat.pow_le_pow_right; linarith
        rw [Nat.le_sub_iff_add_le]; any_goals linarith
      rw [pow_succ']; simp; left; intro h; rw [Nat.sub_eq_zero_iff_le] at h; any_goals linarith
      rw [Nat.ne_zero_iff_zero_lt, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
      rw [show 0+1+1 = 2^1 by simp]; apply Nat.pow_le_pow_right; simp
      rw [Nat.le_sub_iff_add_le]; any_goals linarith
      apply Nat.one_le_pow'
  -- Finally, if $i$ is not of the form $2^j-2$, prove that $a_(i+1)=a_i$
    push_neg at h2pow; use i+1; simp; constructor
    · by_contra!; rw [Nat.lt_iff_add_one_le] at hi
      replace this : n = i + 1 := by linarith
      rw [← Nat.sub_eq_iff_eq_add] at this; symm at this
      contradiction; linarith
    intro hi2; apply_fun fun t => t - 1 at hi2
    rw [Nat.add_sub_cancel, Nat.sub_sub, show 1+1 = 2 by simp] at hi2
    specialize h2pow (Nat.log 2 (i + 1) + 1); contradiction

  -- Prove that the sum in question equals $Nat.log 2 n + 1$, we first use ite_add, ite_div and Finset.sum_ite to rewrite the sum as two sums, then compute the two sum seperately
    simp [a, ite_add, ite_div]; rw [Finset.sum_ite]
  -- Prove that the second sum equals $1$
    have tmph1 : ∑ x ∈ Finset.filter (fun x => ¬x = 2 ^ (Nat.log 2 x + 1) - 1) (Finset.range n), (x - 1 + 1) / (x + 1) = 1 := by
      have : Finset.filter (fun x => ¬x = 2 ^ (Nat.log 2 x + 1) - 1) (Finset.range n) = (Finset.filter (fun x => ¬x = 2 ^ (Nat.log 2 x + 1) - 1) (Finset.range n) \ {0}) ∪ {0} := by
        rw [Finset.sdiff_union_self_eq_union, Finset.union_eq_left.mpr]
        simp; exact npos
      rw [this, Finset.sum_union]; simp
      intro i hi1 hi2 ine0
      push_neg at ine0; rw [Nat.ne_zero_iff_zero_lt] at ine0; linarith; simp
  -- Prove that every term in the first sum equals one, therefore computing the sum is the same as counting elements of the set where the sum takes place
    have tmph2 : (∑ x ∈ Finset.filter (fun x => x = 2 ^ (Nat.log 2 x + 1) - 1) (Finset.range n),
      if 2 * x < n then (2 * x + 1) / (x + 1) else (n - 1 + 1) / (x + 1)) = ∑ x ∈ Finset.filter (fun x => x = 2 ^ (Nat.log 2 x + 1) - 1) (Finset.range n), 1 := by
        apply Finset.sum_congr; rfl
        simp; intro i hi1 hi2; split_ifs
        · rename_i hi3; apply Nat.div_eq_of_lt_le
          any_goals linarith
        rename_i hi3; push_neg at hi3
        have ige1 : 1 ≤ i := by
          rw [hi2, Nat.le_sub_iff_add_le, show 1+1 = 2^1 by simp]
          apply Nat.pow_le_pow_right; any_goals linarith
          apply Nat.one_le_pow'
        apply Nat.div_eq_of_lt_le; rw [one_mul, Nat.sub_add_cancel, Nat.add_one_le_iff]; exact hi1
        linarith; norm_num; rw [Nat.sub_add_cancel]; any_goals linarith
  -- Define a function $f$ between Finset.range $Nat.log 2 n$ to the set in the first sum
    simp [tmph1, tmph2]; let f : ℕ → ℕ := fun i => if i < Nat.log 2 n then 2 ^ (i + 1) - 1 else 0
  -- Prove that $f$ is a bijection
    have tmph3 : Set.BijOn f (Finset.range (Nat.log 2 n)) (Finset.filter (fun x => x = 2 ^ (Nat.log 2 x + 1) - 1) (Finset.range n)) := by
      rw [Set.BijOn]; split_ands
      -- Prove that $f$ maps Finset.range $Nat.log 2 n$ to the set where the first sum takes place
      · intro i; simp [f]; intro hi; split_ifs; constructor
        · rw [Nat.lt_iff_add_one_le, Nat.sub_add_cancel, Nat.pow_le_iff_le_log]
          rw [Nat.add_one_le_iff]; exact hi; any_goals linarith
          apply Nat.one_le_pow'
        · congr; symm; rw [Nat.log_eq_iff]; constructor
          · rw [pow_succ, mul_two, Nat.add_sub_assoc]; simp
            apply Nat.one_le_pow'
          apply Nat.sub_one_lt; positivity
          right; simp; intro h; rw [Nat.sub_eq_zero_iff_le] at h
          nth_rw 2 [show 1 = 2^0 by simp] at h; rw [Nat.pow_le_pow_iff_right] at h
          simp at h; norm_num
        contradiction
      -- Prove that $f$ is injective
      · intro i hi j hj hij; simp [f] at hi hj hij; split_ifs at hij
        rw [← add_left_inj 1, Nat.sub_add_cancel, Nat.sub_add_cancel] at hij
        rw [pow_right_inj] at hij; simp at hij; exact hij; any_goals linarith
        any_goals apply Nat.one_le_pow'
    -- Prove that $f$ is surjective
      intro j; simp [f]; intro hj1 hj2;
      have logjlt : Nat.log 2 j < Nat.log 2 n := by
        rw [← add_left_inj 1, Nat.sub_add_cancel] at hj2
        rw [Nat.lt_iff_add_one_le, hj2, Nat.pow_le_iff_le_log] at hj1
        rw [Nat.lt_iff_add_one_le]; exact hj1; any_goals linarith
        apply Nat.one_le_pow'
      use Nat.log 2 j; constructor; exact logjlt
      split_ifs; symm; exact hj2
  -- Apply Finset.card_nbij to finish the goal
    rw [← Finset.card_nbij f tmph3.mapsTo tmph3.injOn tmph3.surjOn]; simp
-- Prove that $Nat.log 2 n + 1$ is a lower bound to the set of numbers in question
  intro m a abij meq; rw [meq]
-- According to the reference answer, it suffices to prove the following key lemma
  suffices key : ∀ k, ∀ b : ℕ → ℕ, Set.InjOn b (Finset.range (2 ^ k)) → k + 1 ≤
  ∑ i ∈ Finset.range (2 ^ k), (b i + 1) / (i + 1)
  -- Assuming the key lemma, prove the final goal by specializing it to $Nat.log 2 n$ and $a$
  -- As a preparation, we first prove that $a$ is injective on Finset.range $2^(Nat.log 2 n)$
  · have tmph1 : Set.InjOn a (Finset.range (2 ^ Nat.log 2 n)) := by
      intro i hi j hj aij; simp at hi hj
      apply abij.injOn at aij; exact aij
      any_goals simp; linarith
    specialize key (Nat.log 2 n) a tmph1
    nth_rw 2 [show n = 2 ^ (Nat.log 2 n) + (n - 2 ^ (Nat.log 2 n)) by rw [Nat.add_sub_cancel']; exact powlogn]
    rw [Finset.sum_range_add]; apply le_trans key; simp
-- It remains to prove the key lemma, we will proceed by induction on $k$
  intro k; induction k with
  | zero => simp
  | succ k ih =>
  -- In the induction step, we assume the goal holds true for $k$ and prove the case $k+1$.
  -- We split the goal to then cases when there exists a specific number $j$ or not according to the reference answer
    intro b binj; by_cases h : ∃ j, j < 2 ^ k ∧ j + 2 ^ k ≤ b (j + 2 ^ k)
    -- If there were such a $j$, then we can split the sum using Finset.sum_range_add
    · rcases h with ⟨j, ⟨hj1, hj2⟩⟩; rw [pow_succ, mul_two, Finset.sum_range_add]
      have binj' : Set.InjOn b (Finset.range (2 ^ k)) := by
        intro i' hi' j' hj' hij'; simp at hi' hj'
        apply binj at hij'; exact hij'
        any_goals simp; rw [pow_succ]; linarith
    -- Use add_le_add and apply the induction hypothesis to prove the first half of the inequality
      apply add_le_add; apply ih; exact binj'
      suffices : (b (2 ^ k + j) + 1) / (2 ^ k + j + 1) ≤ ∑ x ∈ Finset.range (2 ^ k), (b (2 ^ k + x) + 1) / (2 ^ k + x + 1)
      · apply le_trans _ this; rw [Nat.le_div_iff_mul_le, one_mul]
        rw [Nat.add_one_le_iff, add_comm]; any_goals linarith
      have tmph1 : ∀ x ∈ Finset.range (2 ^ k), 0 ≤ (b (2 ^ k + x) + 1) / (2 ^ k + x + 1) := by simp
      have tmph2 : j ∈ Finset.range (2 ^ k) := by simp; exact hj1
    -- For the second half of the inequality, we isolate the $j$-th term and apply Finset.single_le_sum
      apply Finset.single_le_sum tmph1 tmph2
    push_neg at h
  -- If there were no such $j$, then by applying properties of Nat.nth, we can find such a $m$ according to the reference answer
    obtain ⟨m, ⟨hm1, hm2⟩⟩ : ∃ m, m < 2 ^ (k + 1) ∧ 2 ^ (k + 1) - 1 ≤ b m := by
      set p : ℕ → Prop := fun n => n ∈ b '' (Finset.range (2 ^ (k + 1))) with hp
      have aux : ∀ hf : (setOf p).Finite, hf.toFinset.card = 2 ^ (k + 1) := by
        rw [hp, @Set.setOf_mem_eq]; intro; simp
        rw [Finset.card_image_iff.mpr]; any_goals simp
        simp at binj; exact binj
      obtain ⟨m, ⟨hm1, hm2⟩⟩ : p (Nat.nth p (2 ^ (k + 1) - 1)) := by apply Nat.nth_mem; simp [aux]
      use m; constructor
      · simp at hm1; exact hm1
      rw [hm2]; apply Nat.le_nth; simp [aux]
  -- Prove that $m$ has to be less than $2^k$
    have mlt : m < 2 ^ k := by
      by_contra!; specialize h (m - 2 ^ k) (show _ by rw [pow_succ, mul_two, ← Nat.sub_lt_iff_lt_add] at hm1; exact hm1; exact this)
      repeat rw [Nat.sub_add_cancel] at h
      rw [Nat.lt_iff_add_one_le, ← Nat.le_sub_iff_add_le] at hm1; linarith
      apply Nat.one_le_pow'; exact this
  -- Define a new function $c$ according to the reference answer, then specialize the induction hypothesis ih to $c$
    let c : ℕ → ℕ := fun t => if t = m then b (2 ^ k) else b t
  -- Prove that $c$ is injective on Finset.range (2 ^ k)
    have cinj : Set.InjOn c (Finset.range (2 ^ k)) := by
      intro i hi j hj hij; simp at hi hj
    -- Split to three cases according to the definition of $c$ and prove them case by case
      simp [c] at hij; split_ifs at hij; linarith
      any_goals apply binj at hij; linarith
      any_goals simp; rw [pow_succ, mul_two]; linarith
    specialize ih c cinj; rw [pow_succ, mul_two, Finset.sum_range_add]
  -- Split the sum to two sums by applying Finset.sum_range_add, prove the second sum equals $0$
    have tmph1 : ∑ x ∈ Finset.range (2 ^ k), (b (2 ^ k + x) + 1) / (2 ^ k + x + 1) = 0 := by
      simp; intro i hi
      specialize h i hi; rw [add_comm] at h; linarith
  -- Isolate the term $m$ from the first sum and rewrite the rest terms in $c$
    rw [tmph1, add_zero, Finset.sum_eq_add_sum_diff_singleton (show m ∈ Finset.range (2 ^ k) by simp; exact mlt)]
    have tmph2 : 1 + ∑ i ∈ Finset.range (2 ^ k), (c i + 1) / (i + 1) ≤ (b m + 1) / (m + 1) + ∑ x ∈ Finset.range (2 ^ k) \ {m}, (b x + 1) / (x + 1) := by
      rw [Finset.sum_eq_add_sum_diff_singleton (show m ∈ Finset.range (2 ^ k) by simp; exact mlt)]
    -- Apply add_le_add to rewrite the goal as two inequalities
      rw [← add_assoc]; apply add_le_add
      -- To prove the first inequality, we specialize the hypothesis h at $0$ and rewrite our assumptions until we can use linarith to finish the goal
      · simp [c]; specialize h 0 (show _ by simp); simp at h
        rw [add_comm, ← Nat.add_div_right]; apply Nat.div_le_div_right
        rw [Nat.sub_le_iff_le_add, pow_succ, mul_two] at hm2
        rw [Nat.lt_iff_add_one_le] at mlt h; linarith; simp
    -- To prove the second inequality, we apply Finset.sum_le_sum and use the definition of $c$
      apply Finset.sum_le_sum; intro i hi; simp at hi
      push_neg at hi; rcases hi with ⟨hi1, hi2⟩
      simp [c]; split_ifs; contradiction; rfl
    apply le_trans _ tmph2; rw [add_comm]; simp; exact ih
