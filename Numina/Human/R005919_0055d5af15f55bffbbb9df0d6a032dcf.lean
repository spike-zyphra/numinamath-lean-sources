import Mathlib

/- Compute the sum of all integers $n$ such that $n^{2}-3000$ is a perfect square.-/
theorem number_theory_610722 :
    ∑ᶠ n ∈ {n : ℤ | IsSquare (n ^ 2 - 3000)}, n = 0 := by
  -- Show a lemma that would be useful later.
  have hlm (a b : ℤ) (ha : 0 < a) (h : a * b = 3000) : a + b ≤ 3001 := by
    -- We shall also have 0 < b.
    have hb : 0 < b := by
      nlinarith
    -- Convert the problem to a² + 3000 ≤ 3001a, which becomes a quadratic inequality. We further factorize a² - 3001a + 3000 = (a - 1500.5)² - 1499.5².
    suffices (a - 1500.5 : ℚ) ^ 2 ≤ 1499.5 ^ 2 by
      nlinarith
    -- We have 1 ≤ a ≤ 3000.
    replace hb : a.natAbs ∣ 3000 := by
      zify
      simp [le_of_lt ha]
      rw [<-h]
      apply dvd_mul_right
    apply Nat.le_of_dvd (by norm_num) at hb
    zify at hb
    rw [abs_of_nonneg (le_of_lt ha)] at hb
    replace ha : 1 ≤ a := by
      linarith
    qify at ha hb
    -- We have |a - 1500.5| ≤ 1499.5.
    rw [sq_le_sq, abs_le]
    simp [abs_of_nonneg (show 0 ≤ (1499.5 : ℚ) by norm_num)]
    constructor
    <;> linarith
  -- Define two sets that corresponds to the positive and negative integers satisfying the condition, respectively.
  let Spos := {n : ℤ | n > 0 ∧ IsSquare (n ^ 2 - 3000)}
  let Sneg := {n : ℤ | n < 0 ∧ IsSquare (n ^ 2 - 3000)}
  -- Show that Spos and Sneg are disjoint.
  have h₀ : Disjoint Spos Sneg := by
    simp [Set.disjoint_iff]
    ext n
    simp [Spos, Sneg]
    intro _ _ _ _
    linarith
  -- Show that the union of Spos and Sneg is {n : ℤ | IsSquare (n ^ 2 - 3000)}.
  have h₁ : Spos ∪ Sneg = {n : ℤ | IsSquare (n ^ 2 - 3000)} := by
    ext n
    simp [Spos, Sneg]
    rw [<-or_and_right]
    constructor
    . rintro ⟨hn, _⟩
      by_contra!
      simp_all
    . intro h
      simp_all
      -- Note that n = 0 is incompatible with the condition that n² - 3000 is a square.
      by_contra!
      rw [<-this] at h
      simp at h
      rcases h with ⟨y, h⟩
      linarith [sq_nonneg y]
  -- Let Ssupp be the set of integers n such that |n| ≤ 1500, we will have Spos ∪ Sneg ⊆ Ssupp.
  let Ssupp := {n : ℤ | n ∈ Finset.Icc (-1500) 1500}
  -- Show that Ssupp is finite.
  have h₂ : Ssupp.Finite := by
    -- Note that Ssupp is just Finset.Icc (-1500) 1500.
    suffices Ssupp = Finset.Icc (-1500) 1500 by
      rw [this]
      apply Finset.finite_toSet
    simp [Ssupp]
    ext n
    simp
  -- Show that Spos and Sneg are positive.
  have h₃ : Spos.Finite := by
    apply Set.Finite.subset h₂
    rw [Set.subset_def]
    simp [Spos, Ssupp]
    rintro n hn h
    -- Now we have n² - 3000 being a square (of some non-negative number), we shall show that n ≤ 1500.
    obtain ⟨m, h⟩ := h
    rw [<-abs_mul_abs_self] at h
    replace h : (n + |m|) * (n - |m|) = 3000 := by
      linarith
    -- Use the lemma we proved before.
    apply hlm _ _ (by positivity) at h
    simp at h
    omega
  have h₄ : Sneg.Finite := by
    apply Set.Finite.subset h₂
    rw [Set.subset_def]
    simp [Sneg, Ssupp]
    rintro n hn h
    apply Int.neg_pos_of_neg at hn
    -- Now we have n² - 3000 being a square (of some non-negative number), we shall show that n ≥ -1500.
    obtain ⟨m, h⟩ := h
    rw [<-abs_mul_abs_self] at h
    replace h : (-n + |m|) * (-n - |m|) = 3000 := by
      linarith
    -- Use the lemma we proved before.
    apply hlm _ _ (by positivity) at h
    simp at h
    omega
  -- Show that sum of the elements of the original set is zero.
  rw [<-h₁, finsum_mem_union h₀ h₃ h₄, finsum_mem_eq_finite_toFinset_sum _ h₃, finsum_mem_eq_finite_toFinset_sum _ h₄]
  -- It suffices to show that the sum of Spos is equal to the negative of sum of Sneg.
  rw [add_eq_zero_iff_eq_neg, <-Finset.sum_neg_distrib]
  -- There is a natural bijection between Spos and Sneg, which is n ↦ -n.
  apply @Finset.sum_bijective _ _ _ _ h₃.toFinset h₄.toFinset _ _ (fun n => -n)
  . -- Show that the function is bijective.
    simp [Function.Bijective]
    intro n m h
    simp_all
  . -- Show that n ∈ Spos iff -n ∈ Sneg.
    intro n
    simp [Spos, Sneg]
  . -- Show that for n ∈ Spos, n = -(-n).
    simp
