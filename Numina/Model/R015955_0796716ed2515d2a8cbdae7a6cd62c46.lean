import Mathlib

theorem algebra_262383 {a d : ℤ} (h₀ : a + 16 * d = 52) (h₁ : a + 29 * d = 13)
    (S : ℕ → ℤ) (hS : ∀ n, S n = ∑ i in Finset.range n, (a + d * i)) :
    IsGreatest {x | ∃ n, x = S n ∧ n ≤ 34} 1717 := by

  have hd : d = -3 := by
    omega

  have ha : a = 100 := by
    rw [hd] at h₀
    omega

  constructor
  · -- Show 1717 is in the set
    use 34 
    constructor
    · -- Show x = S 34
      have h34 : S 34 = 1717 := by 
        rw [hS 34] 
        rw [ha, hd]
        norm_num [Finset.sum_range_succ]
      linarith 
    · -- Show 34 ≤ 34 
      omega 
  · -- Show 1717 is greatest
    intro x hx 
    rcases hx with ⟨n, hn1, hn2⟩ 
    have h5 : x ≤ 1717 := by 
      rw [hn1]
      have h6 : n ≤ 34 := by linarith 
      have h7 : S n = ∑ i in Finset.range n, (a + d * i) := hS n 
      rw [h7] 
      rw [ha, hd]
      have h8 : ∀ (n : ℕ), n ≤ 34 → (∑ i in Finset.range n, (100 + (-3 : ℤ) * i) : ℤ) ≤ 1717 := by 
        intro n hn 
        interval_cases n <;> norm_num [Finset.sum_range_succ]
      specialize h8 n (by linarith)
      linarith 
    linarith