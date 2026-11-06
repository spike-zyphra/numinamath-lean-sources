import Mathlib

/-
Let $k_0$ be an integer greater than $1$. Let $N = k_0^2-1$. Let $\tau(m)$ denote the number of positive divisors of an integer $m$. Determine the number of positive factors of $N^2$ that do not divide $N$. Show that this number is equal to $\tau(N^2) - \tau(N)$.
-/


--Use the definition to rewrite the set in the statement.
lemma l1 (N:ℕ) (Npos: 0 < N):
{x:ℕ | x ∣ N^2 ∧ (¬ x∣ N)} = Nat.divisors (N^2) \ Nat.divisors (N) := by
  ext x
  simp

  constructor

  intro ⟨h1,h2⟩
  constructor
  simp [h1]
  omega
  intro h
  contradiction

  intro ⟨h1,h2⟩
  constructor
  exact h1.left
  by_contra dd
  simp [dd] at h2
  omega

--Every divisor of N is a divisor of N^2.
lemma l2 (N:ℕ):
  Nat.divisors (N) ⊆ Nat.divisors (N^2) := by
  intro x
  simp
  intro h nne0
  simp [nne0]

  obtain ⟨d,hd⟩ := h
  use d*N
  rw [hd]
  ring
lemma l3 (N:ℕ):
(Nat.divisors (N^2) \ Nat.divisors (N)).card = (Nat.divisors (N^2)).card - (Nat.divisors (N)).card := by
  refine Finset.card_sdiff ?_
  apply l2


theorem number_theory_641429 (k0 N: ℕ) (k0g1: 1 < k0) (hN : N = k0^2 - 1):
{x:ℕ | x ∣ N^2 ∧ (¬ x∣ N)}.ncard = (Nat.divisors (N^2)).card - (Nat.divisors N).card := by

  --Rewrite our set by the first lemma and then apply Lemma 3.
  rw [l1]
  simp
  norm_cast
  apply l3
  
  rw [hN]
  field_simp
  exact k0g1
  