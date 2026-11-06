import Mathlib

theorem algebra_296505 (n : ℤ) : ¬ 121 ∣ n^2 + 2 * n + 12 := by
  intro h
  have h1 : n ^ 2 + 2 * n + 12 = 121 * ( (n ^ 2 + 2 * n + 12) / 121 ) := by 
    omega
  have h2 : (n ^ 2 + 2 * n + 12) % 11 = 0 := by
    omega
  have h3 : n % 11 = 10 := by 
    have h2' : (n ^ 2 + 2 * n + 12) % 11 = 0 := by 
      omega
    have h3' : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by
      omega
    rcases h3' with (h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3' | h3') <;> simp [h3', pow_two, Int.add_emod, Int.mul_emod] at h2' <;> tauto
  have h4 : ∃ k : ℤ, n = 11 * k + 10 := by
    have h5 : n % 11 = 10 := h3
    refine' ⟨(n - 10) / 11, by omega⟩
  rcases h4 with ⟨k, hk⟩
  have h5 : n ^ 2 + 2 * n + 12 = 121 * (k ^ 2 + 2 * k) + 132 := by
    rw [hk]
    ring
  have h6 : (n ^ 2 + 2 * n + 12) % 121 = 0 := by
    omega
  rw [h5] at h6
  omega