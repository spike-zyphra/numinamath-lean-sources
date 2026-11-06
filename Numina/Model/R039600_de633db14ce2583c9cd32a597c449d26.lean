import Mathlib

theorem number_theory_223925 : ∀ n : ℤ, ¬ 121 ∣ n^2 + 3 * n + 5 := by
  intro n
  intro h
  have h1 : (n^2 + 3 * n + 5 : ℤ) % 121 = 0 := by 
    omega
  have h2 : (n^2 + 3 * n + 5) % 11 = 0 := by
    omega
  -- Determine n mod 11
  have h3 : n % 11 = 4 := by 
    have h4 : (n^2 + 3 * n + 5) % 11 = 0 := h2
    have : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by 
      omega 
    rcases this with (h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod] at h4 <;> try { tauto }
  -- Assume n = 11k + 4
  have h4 : ∃ k : ℤ, n = 11 * k + 4 := by 
    have : n % 11 = 4 := h3
    refine' ⟨(n - 4) / 11, by omega⟩
  rcases h4 with ⟨k, hk⟩
  have h5 : (n^2 + 3 * n + 5 : ℤ) = 121 * (k^2 + k) + 33 := by 
    rw [hk]
    ring_nf
  have h6 : (n^2 + 3 * n + 5 : ℤ) % 121 = 0 := h1
  omega