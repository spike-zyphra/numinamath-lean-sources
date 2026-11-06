import Mathlib

/- Let $\tau(n)$ denote the number of positive integer divisors of $n$. Find the sum of the six least positive integers $n$ that are solutions to $\tau (n) + \tau (n+1) = 7$. -/
theorem number_theory_97859 (τ : ℕ → ℕ) (hτ : ∀ n, τ n = (Nat.divisors n).card) :
    (Nat.nth {n | τ n + τ (n + 1) = 7} 0) + (Nat.nth {n | τ n + τ (n + 1) = 7} 1) +
    (Nat.nth {n | τ n + τ (n + 1) = 7} 2) + (Nat.nth {n | τ n + τ (n + 1) = 7} 3) +
    (Nat.nth {n | τ n + τ (n + 1) = 7} 4) + (Nat.nth {n | τ n + τ (n + 1) = 7} 5) = 540 := by
  have : τ = fun n ↦ n.divisors.card := by ext; exact hτ _
  subst this
  set p : ℕ → Prop := fun n ↦ n.divisors.card + (n + 1).divisors.card = 7 with hp

  -- We prove an auxiliary lemma that allows ut to show the nth number satisfying a predicate p is k
  have aux {n k : ℕ}
      (h : Nat.count p n = k := by native_decide)
      (h' : Nat.count p n.succ = k.succ := by native_decide) :
      Nat.nth p k = n := by
    have hp : p n := by
      by_contra! h_contra
      rw [Nat.count_succ, h] at h'
      simp [h_contra] at h'
    have h₁ : n ≤ Nat.nth p k := by
      rw [← h]
      apply Nat.le_nth_count'
      exact ⟨n, ⟨hp, le_refl _⟩⟩
    have h₂ : Nat.nth p k ≤ n := by
      by_contra! h_contra
      change n + 1 ≤ Nat.nth p k at h_contra
      have := Nat.le_nth_of_count_le h_contra
      rw [h'] at this
      omega
    exact le_antisymm h₂ h₁

  -- We prove auxiliary lemmas that shows the nth number satisfying p is k
  have h₁ : Nat.nth p 0 = 8 := aux
  have h₂ : Nat.nth p 1 = 9 := aux
  have h₃ : Nat.nth p 2 = 16 := aux
  have h₄ : Nat.nth p 3 = 25 := aux
  have h₅ : Nat.nth p 4 = 121 := aux
  have h₆ : Nat.nth p 5 = 361 := aux

  -- Finally, we substitute these into the problem statement
  rw [setOf, h₁, h₂, h₃, h₄, h₅, h₆]