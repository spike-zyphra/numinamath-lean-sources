import Mathlib

open GCDMonoid (gcd)

theorem number_theory_4505 {a : ℕ → ℤ} (n : ℕ) (d : ℤ) : (∀ i ∈ Finset.range (n+2), d ∣ a i) ↔
    (∀ i ∈ Finset.range n, d ∣ a i) ∧ d ∣ Int.gcd (a n) (a (n+1)) := by
  constructor
  · -- First direction: ∀ i ∈ range (n + 2), d ∣ a i → (∀ i ∈ range n, d ∣ a i) ∧ d ∣ gcd
    intro h
    constructor
    · -- ∀ i ∈ range n, d ∣ a i
      intro i hi
      have h1 : i ∈ Finset.range (n + 2) := by
        have h2 : i < n + 2 := by
          have h1 : i < n := by
            simpa using hi
          omega
        simp at *
        <;> tauto
      apply h
      exact h1
    · -- d ∣ gcd
      have ha1 : d ∣ a n := by
        apply h
        simp
      have ha2 : d ∣ a (n + 1) := by
        apply h
        simp
      apply Int.dvd_gcd
      exact ha1
      exact ha2
  · -- Second direction: (∀ i ∈ range n, d ∣ a i) ∧ d ∣ gcd
    intro h
    rcases h with ⟨h1, h2⟩
    intro i hi
    have h3 : i < n + 2 := by
      simp at hi ⊢
      omega
    by_cases h4 : i < n
    · -- Case i < n
      have h5 : i ∈ Finset.range n := by
        simp at h4 ⊢
        all_goals omega
      apply h1
      exact h5
    · -- Case i ≥ n
      have h5 : i = n ∨ i = n + 1 := by 
        omega 
      rcases h5 with (r | r)
      · -- Case i = n
        rw [r]
        have ha3 : d ∣ a n := by 
          have h4 : d ∣ Int.gcd (a n) (a (n+1)) := h2 
          have h5 : (Int.gcd (a n) (a (n+1)) : ℤ) ∣ (a n : ℤ) := by 
            simp [Int.gcd_dvd_left] 
          have h6 : d ∣ (a n : ℤ) := by 
            exact dvd_trans h4 h5 
          exact h6 
        exact ha3 
      · -- Case i = n + 1
        rw [r]
        have ha3 : d ∣ a (n + 1) := by 
          have h4 : d ∣ Int.gcd (a n) (a (n+1)) := h2 
          have h5 : (Int.gcd (a n) (a (n+1)) : ℤ) ∣ (a (n + 1) : ℤ) := by 
            simp [Int.gcd_dvd_right] 
          have h6 : d ∣ (a (n + 1) : ℤ) := by 
            exact dvd_trans h4 h5 
          exact h6 
        exact ha3