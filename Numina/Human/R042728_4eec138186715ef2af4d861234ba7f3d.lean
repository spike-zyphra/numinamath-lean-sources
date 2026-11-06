import Mathlib

/- What is the greatest number of consecutive integers whose sum is 45?
(A) 9(B) 25(C) 45(D) 90(E) 120-/

theorem algebra_93047 : IsGreatest {k : ℕ | ∃ a : ℤ, ∑ i ∈ Finset.range k, (a + i + 1) = 45} 90 := by {
  -- We begin by showing that it suffices to show that whenever a sum of consecutive integers is 45 then the length must divide 90.
  suffices : ∀ k : ℕ, (∃ (a : ℤ), ∑ i ∈ Finset.range k, (a + i + 1) = 45) → k ∣ 90
  constructor
  -- We first show that (under this assumption) 90 has the required property, which doesn't really require it.
  simp
  use -45
  norm_num

  -- We now show, using our assumption, that any integer with the desired property is at most 90. This is immediate because we know that it divides 90.
  unfold upperBounds
  simp
  intros k a h
  apply Nat.le_of_dvd (by norm_num)
  apply this
  use a

  -- We show as an auxiliary lemma the classical result for sums of consecutive natural numbers, when interpreting them as integers. This is obvious, but the typecasting makes it convenient to record it.
  have hsum : ∀ k : ℕ, (∑ i ∈ Finset.range k, (i : ℤ))*2 = k * (k-1) := by {
    intro k
    by_cases hk0 : k = 0
    rw [hk0]
    trivial
    have : ∑ i ∈ Finset.range k, (i : ℤ) = ∑ i ∈ Finset.range k, i := by norm_num
    rw [this]
    rw [←Ne.eq_def,←Nat.one_le_iff_ne_zero] at hk0
    norm_cast
    rw [Finset.sum_range_id_mul_two]
  }

  -- We now start showing our actual claim, that whenever a sum of consecutive integers is 45 then the length must divide 90.
  intros k h
  rcases h with ⟨a,ha⟩ 
  -- Here we are starting to evaluate the sum in question.
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_const,Finset.sum_const] at ha
  simp at ha
  by_cases hk1 : 1 ≤ k
  have ha' : (k : ℤ)*(2*a + k + 1) = 90 := by {
    have : (90 : ℤ) = 45 * 2 := by norm_num
    rw [this,←ha]
    rw [mul_add,mul_add,add_mul,add_mul,hsum] -- Here we use Gauss' sum of integers
    ring
  }
  rw [←Int.natCast_dvd_natCast]
  use 2*a+k+1 -- Since we have written 90 as a product of k and another integers, the claim follows.
  rw [ha'] 
  trivial
  
  simp at hk1
  rw [hk1] at ha
  simp at ha

}