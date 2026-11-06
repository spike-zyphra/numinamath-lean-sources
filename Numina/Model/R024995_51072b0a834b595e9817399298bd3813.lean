import Mathlib

theorem number_theory_129492 (n : ℤ) :
    IsGreatest {x | x ∣ (5 * n - 7) ∧ x ∣ (3 * n + 2)} 31 ↔
    ∃ k, n = 31 * k - 11 := by
  constructor
  · -- Assume 31 is greatest element in the set of common divisors
    intro h
    have h1 : (31 ∣ (5 * n - 7) ∧ 31 ∣ (3 * n + 2)) := by 
      constructor
      · -- Show 31 divides 5n - 7
        have h4 : 31 ∈ {x | x ∣ (5 * n - 7) ∧ x ∣ (3 * n + 2)} := by
          exact h.1
        have h5 : 31 ∣ (5 * n - 7) := by 
          simpa using h4.1
        assumption
      · -- Show 31 divides 3n + 2
        have h4 : 31 ∈ {x | x ∣ (5 * n - 7) ∧ x ∣ (3 * n + 2)} := by
          exact h.1
        have h5 : 31 ∣ (3 * n + 2) := by 
          simpa using h4.2
        assumption
    have h2 : n % 31 = 20 := by
      omega 
    refine' ⟨(n / 31 + 1), by omega⟩ 
  · -- Assume ∃ k, n = 31 * k - 11
    rintro ⟨k, hk⟩
    constructor
    · -- Show 31 is in the set
      constructor
      · -- Show 31 divides 5n - 7
        rw [hk]
        use 5 * k - 2
        ring_nf
      · -- Show 31 divides 3n + 2
        rw [hk]
        use 3 * k - 1
        ring_nf
    · -- Show no greater element is in the set
      intro d hd
      rcases hd with ⟨h1, h2⟩
      have h3 : d ∣ (31 : ℤ) := by
        have h11 : d ∣ (5 * n - 7 : ℤ) := h1
        have h12 : d ∣ (3 * n + 2 : ℤ) := h2
        have h13 : d ∣ (-3 * (5 * n - 7) + 5 * (3 * n + 2) : ℤ) := by
          apply Dvd.dvd.add
          · apply Dvd.dvd.mul_left
            exact h1
          · apply Dvd.dvd.mul_left
            exact h2
        have h14 : (-3 * (5 * n - 7) + 5 * (3 * n + 2) : ℤ) = 31 := by
          linarith [hk]
        rw [h14] at h13
        exact h13
      have h4 : d ≤ 31 := by
        apply Int.le_of_dvd (by norm_num) h3
      have h5 : d ≤ (31 : ℤ) := h4
      linarith