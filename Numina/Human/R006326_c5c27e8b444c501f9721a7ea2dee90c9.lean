import Mathlib

/-
Let $A$ and $B$ be positive integers. Determine the sum of all integers $n$ such that $n>1$, $A$ is divisible by $n$, and $B$ is divisible by $n$. Show that this sum is equal to $\sigma_1(\gcd(A, B)) - 1$, where $\sigma_1(k)$ denotes the sum of the positive divisors of $k$.
-/

--We prove that the set appearing in the theorem differ by {1}.
lemma l1 (A B : ℕ) (Apos: 0 < A) (Bpos : 0 < B):
(Nat.divisors A ∩ Nat.divisors B).filter (fun x => 1 < x) ∪ {1}
=
(Nat.divisors (Nat.gcd A B)) := by
  ext n
  simp

  constructor <;> intro h

  rcases h with h | h
  obtain ⟨h1,h3⟩ := h; obtain ⟨h1,h2⟩ := h1
  obtain ⟨ndA,hA⟩ := h1
  obtain ⟨ndB,hB⟩ := h2
  constructor
  exact Nat.dvd_gcd ndA ndB
  rw [Nat.gcd_eq_zero_iff]
  simp [hA,hB]
  rw [h]
  constructor
  simp
  rw [Nat.gcd_eq_zero_iff]
  omega

  obtain ⟨h1,h2⟩ := h
  rw [Nat.dvd_gcd_iff] at h1
  obtain ⟨ndA,ndB⟩ := h1
  rw [Nat.gcd_eq_zero_iff] at h2
  have nAe0 : ¬ A = 0 := by omega
  have nBe0 : ¬ B = 0 := by omega
  simp [ndA,nAe0,ndB,nBe0]
  
  by_cases ne0 : n = 0
  simp [ne0] at ndA; contradiction
  omega


theorem number_theory_635895 (A B : ℕ) (Apos: 0 < A) (Bpos : 0 < B):
∑ d ∈ (Nat.divisors A ∩ Nat.divisors B).filter (fun x => 1 < x), d
=
(∑ d∈(Nat.divisors (Nat.gcd A B)), d) - 1 := by
  
  --The theorem now follows from the lemma immediately, since ∑ d ∈ {1},d = 1.
  have cla := by apply l1 A B Apos Bpos
  have t1 : ∑ d ∈ ((Nat.divisors A ∩ Nat.divisors B).filter (fun x => 1 < x) ∪ {1}), d = ∑ d ∈ ((Nat.divisors (Nat.gcd A B))), d := by
    rw [cla]
  rw [Finset.sum_union] at t1
  simp  at t1
  rw [← t1]
  rw [Nat.add_sub_cancel]
  simp