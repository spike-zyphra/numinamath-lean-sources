import Mathlib

/-
Let $N$ be an integer greater than or equal to 3. The sum of three positive integers (not necessarily distinct) is $N$. By subtracting them pairwise (the larger minus the smaller), three difference numbers are obtained. Show that the maximum possible value of the sum of these three difference numbers is $2(N-3)$.
-/

theorem number_theory_638559 (N: ℕ) (hN: 3 ≤ N):
IsGreatest {x:ℕ | ∃a:ℕ,∃b:ℕ, ∃c:ℕ, 0<a ∧ a ≤ b ∧ b ≤ c ∧ a+b+c = N ∧ x = (b-a) + (c-a) + (c-b)} (2*(N-3)) := by

  unfold IsGreatest upperBounds
  simp

  --2*(N-3) can be achieved by 1 1 N-2.
  constructor
  use 1
  simp
  use 1
  simp
  use N-2
  omega

  --2*(N-3) is the greatest. (b-a) + (c-a) + (c-b) = 2\*c-2\*a. We have a is at least 1 and c is at most n-2, so the largest value is at most 2(N-3).
  intro r a apos b bgea c cgeb hs h
  have req : r = 2*c-2*a := by omega
  have age1 : 1 ≤ a := by omega
  have clenm2 : c ≤ N - 2 := by omega
  omega
  