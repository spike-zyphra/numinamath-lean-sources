import Mathlib

theorem number_theory_189291 : ¬∃ n : ℤ, 121 ∣ n^2 + 3 * n + 5 := by
  rintro ⟨n, hn⟩
  have h2 : (n ^ 2 + 3 * n + 5) % 121 = 0 := by 
    omega
  have h3 : (n ^ 2 + 3 * n + 5) % 11 = 0 := by 
    omega
  have h4 : n % 11 = 4 := by
    have h5 : (n ^ 2 + 3 * n + 5) % 11 = 0 := h3
    have h6 : n % 11 = 0 ∨ n % 11 = 1 ∨ n % 11 = 2 ∨ n % 11 = 3 ∨ n % 11 = 4 ∨ n % 11 = 5 ∨ n % 11 = 6 ∨ n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 9 ∨ n % 11 = 10 := by 
      omega
    rcases h6 with (h | h | h | h | h | h | h | h | h | h | h) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h] at h5 <;> tauto
  have h5 : ∃ k : ℤ, n = 4 + 11 * k := by 
    refine' ⟨(n - 4) / 11, by omega⟩
  rcases h5 with ⟨k, hk⟩
  have eq1 : n^2 + 3 * n + 5 = 33 + 121 * (k + k^2) := by
    rw [hk]
    ring_nf
  omega