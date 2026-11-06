import Mathlib

/- 13) Let $X$ be a set of positive integers. It is known that $X$ contains at least one element greater than 1 and that, whenever it contains a certain number $n$, it also contains all numbers greater than $n$ except, possibly, the multiples of $n$. Which of the following statements is certainly correct?

(A) $X$ is a finite set

(B) the set $X$ and the set of positive integers that do not belong to $X$ are both infinite

(C) $X$ contains all prime numbers

(D) there exists a number $m$ such that $X$ contains all integers greater than $m$

(E) $X$ is equal to the set of all positive integers -/

theorem number_theory_127886 (X : Set ℕ) (hpos: ∀n, n∈X → 0<n) (h: ∃ m:ℕ, 1<m ∧ m ∈ X) (hX : ∀ n ∈ X, ∀ m > n, m ∈ X ∨ (n ∣ m)) : ∃ m, ∀ n, m < n → n ∈ X := by
  obtain ⟨m, ⟨mg1, hmx⟩⟩ := h 
  
  use m
  intro n hmn

  --We will prove that if n>1 is in the set, then every number ≥ n is also in the set.
  have cla : ∀ s : ℕ, ((m + s) ∈ X) := by 
    intro s
    induction' s with s hs

    simp; assumption

    have : m+(s+1) ∈ X ∨ m+s ∣ m+(s+1) := by 
      apply hX
      assumption
      omega
    rcases this with h1 | h2
    assumption
    
    --It cannot happen that m+s ∣ m+(s+1), since otherwise m+s = 1 and we know that m > 1.
    exfalso
    rw [←add_assoc] at h2
    have : (m+s) ∣ 1 := by exact Nat.dvd_add_self_left.mp h2
    have : m+s = 1 := by exact Nat.eq_one_of_dvd_one this
    linarith

  have : ∃ a : ℕ, m+a = n := by use n-m; omega
  obtain ⟨a, ha⟩ := this
  rw [←ha]; 
  exact cla a
  