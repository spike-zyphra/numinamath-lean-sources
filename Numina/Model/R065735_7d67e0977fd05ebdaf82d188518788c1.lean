import Mathlib

theorem number_theory_40437 {n : ℤ} (hn : n > 1) (h : ∃ k, k^2 = 3 * n + 1) :
    ∃ a b c, a^2 + b^2 + c^2 = n + 1 := by 
  rcases h with ⟨k, hk⟩
  have h1 : k^2 % 3 = 1 := by 
    omega 
  have h2 : k % 3 = 1 ∨ k % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h3 : k % 3 = 0 := by 
      omega
    have h4 : k^2 % 3 = 0 := by 
      simp [Int.add_emod, pow_two, Int.mul_emod, h3]
      <;> omega
    omega
  cases h2 with 
  | inl h1l =>
    have h40 : ∃ t : ℤ, k = 3 * t + 1 := by 
      refine' ⟨(k - 1) / 3, by omega⟩
    rcases h40 with ⟨t, ht⟩
    have h0' : n = 3 * t^2 + 2 * t := by 
      rw [ht] at hk
      nlinarith
    use t, t + 1, - t
    nlinarith [h0']
  | inr h1r =>
    have h50 : ∃ t : ℤ, k = 3 * t + 2 := by 
      refine' ⟨(k - 2) / 3, by omega⟩
    rcases h50 with ⟨t, ht⟩
    have h0' : n = 3 * t^2 + 4 * t + 1 := by 
      rw [ht] at hk
      nlinarith
    have : n + 1 = 3 * t^2 + 4 * t + 2 := by 
      linarith
    use t + 1, t + 1, t
    nlinarith [show n + 1 = 3 * t^2 + 4 * t + 2 by linarith]