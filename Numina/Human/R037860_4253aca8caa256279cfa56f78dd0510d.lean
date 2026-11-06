import Mathlib
set_option maxRecDepth 2000
/-
PROBLEM: Find the largest possible value of k for which 3^11 is expressible as the sum of k consecutive positive integers.
-/
theorem number_theory_95074 :
IsGreatest {k | ∃ n : ℕ, 3^11 = ∑ i ∈ Finset.range k, (n + i)} 486 := by {
 constructor
 -- Show that 3^11 is expressible as the sum of 486 consecutive integers
 simp
 use 122
 trivial
 -- Show that if 3^11 is expressible as the sum of k consecutive integers then k ≤ 486
 rw [mem_upperBounds]
 intros k hk
 simp at hk
 rcases hk with ⟨n,hk⟩
 have h' : 177147* 2 = (∑ i ∈ Finset.range k, (n + i))*2 := by { rw [hk]}
 simp at h'
 -- Evaluate the sum using the standard equality of Gauss for the sum of the first n integers. This implies that k ∣ 2*3^11
 rw [Finset.sum_add_distrib,Nat.add_mul,Finset.sum_range_id_mul_two,Finset.sum_const,Finset.card_range] at h'
 simp at h'
 rw [mul_assoc,←Nat.mul_add] at h'
 have : 354294 = 2*3^11 := by norm_num
 rw [this] at h'
 have hkdiv : k ∣ 2*3^11 := by {
  rw [h']
  simp
 }
 -- Show that this evaluation in fact implies that k < 3^6
 have hk2le : k * (k - 1) ≤ 2*3^11 := by {
  have : (k-1) ≤ n*2 + (k - 1) := by simp
  have := Nat.mul_le_mul_left k this
  rw [←h'] at this
  exact this
 }
 have hkle : k < 3^6 := by {
  contrapose hk2le
  simp at hk2le
  simp
  have : 728 ≤ k - 1 := by{
   rw [Nat.le_sub_iff_add_le _]
   trivial
   contrapose hkdiv
   simp at hkdiv
   rw [hkdiv]
   trivial
  }
  have hk2in : 729 * 728 ≤ k * (k-1) := by {
   apply Nat.mul_le_mul
   exact hk2le
   exact this
  }
  have : 354294 < 729 * 728 := by trivial
  exact lt_of_lt_of_le this hk2in
 }
 have hkdiv' : k ∣ 2*3^11 ∧ 2*3^11 ≠ 0 := by constructor; exact hkdiv; norm_num
 rw [←Nat.mem_divisors] at hkdiv'
 -- Calculate all the divisors of 2*3^11
 have : (2 * 3 ^ 11).divisors = {1, 2, 3, 6, 9, 18, 27, 54, 81, 162, 243, 486, 729, 1458, 2187, 4374, 6561, 13122, 19683, 39366, 59049, 118098, 177147, 354294} := by {
  rw [Nat.divisors_mul]
  have hdiv2: Nat.divisors 2 = {1,2} := by trivial
  rw [hdiv2]
  have hdiv311 : Nat.divisors (3^11) = {3^0,3^1,3^2,3^3,3^4,3^5,3^6,3^7,3^8,3^9,3^10,3^11} := by {rw [Nat.divisors_prime_pow]; trivial; trivial}
  rw [hdiv311]
  trivial
  }
 rw [this] at hkdiv'
 have hkel : k ∈ ({1, 2, 3, 6, 9, 18, 27, 54, 81, 162, 243, 486} : Finset ℕ) ∨ k ∈ ({729, 1458, 2187, 4374, 6561, 13122, 19683, 39366, 59049, 118098,
  177147, 354294} : Finset ℕ) := by {
   rw [←Finset.mem_union]
   exact hkdiv'
  }
 -- Go through all the divisors individually and show that they are either ≤ 486 or ≥ 3^6, a contradiction.
 rcases hkel with hle | hgt
 simp at hle
 rcases hle with h | h | h | h | h | h | h | h | h | h | h | h | h
 all_goals try { rw [h]; trivial}
 simp

 simp at hgt
 rcases hgt with h | h | h | h | h | h | h | h | h | h | h | h
 all_goals try {rw [h] at hkle; contradiction}
}