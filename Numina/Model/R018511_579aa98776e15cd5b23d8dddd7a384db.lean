import Mathlib

theorem number_theory_8974 {g : ℕ → ℕ}
    (hg : ∀ n, ∑ d in n.divisors, g d = Nat.totient n) :
    g 50 = 0 := by
  have eq1 := hg 1
  have eq2 := hg 2
  have eq5 := hg 5
  have eq10 := hg 10
  have eq25 := hg 25
  have eq50 := hg 50
  have h1 : g 1 = 1 := by
    have h1 : ∑ d in (1 : ℕ).divisors, g d = Nat.totient 1 := eq1
    rw [show (1 : ℕ).divisors = ({1} : Finset ℕ) by decide] at h1
    rw [show Nat.totient 1 = 1 by decide] at h1
    simp at h1 ⊢
    all_goals omega
  have h2 : g 2 = 0 := by
    have h2 : ∑ d in (2 : ℕ).divisors, g d = Nat.totient 2 := eq2
    rw [show (2 : ℕ).divisors = ({1, 2} : Finset ℕ) by decide] at h2
    rw [show Nat.totient 2 = 1 by decide] at h2
    simp [h1] at h2 ⊢
    all_goals omega
  have h5 : g 5 = 3 := by 
    have h5 : ∑ d in (5 : ℕ).divisors, g d = Nat.totient 5 := eq5
    rw [show (5 : ℕ).divisors = ({1, 5} : Finset ℕ) by decide] at h5
    rw [show Nat.totient 5 = 4 by decide] at h5
    simp [h1] at h5 ⊢
    all_goals omega
  have h10 : g 10 = 0 := by
    have h10 : ∑ d in (10 : ℕ).divisors, g d = Nat.totient 10 := eq10
    rw [show (10 : ℕ).divisors = ({1, 2, 5, 10} : Finset ℕ) by decide] at h10
    rw [show Nat.totient 10 = 4 by decide] at h10
    simp [h1, h2, h5] at h10 ⊢
    all_goals omega
  have h25 : g 25 = 16 := by
    have h25 : ∑ d in (25 : ℕ).divisors, g d = Nat.totient 25 := eq25
    rw [show (25 : ℕ).divisors = ({1, 5, 25} : Finset ℕ) by decide] at h25
    rw [show Nat.totient 25 = 20 by decide] at h25
    simp [h1, h5] at h25 ⊢
    all_goals omega
  have h50 : g 50 = 0 := by
    have h50 : ∑ d in (50 : ℕ).divisors, g d = Nat.totient 50 := eq50
    rw [show (50 : ℕ).divisors = ({1, 2, 5, 10, 25, 50} : Finset ℕ) by native_decide] at h50
    rw [show Nat.totient 50 = 20 by native_decide] at h50
    simp [h1, h2, h5, h10, h25] at h50 ⊢
    all_goals omega
  exact h50