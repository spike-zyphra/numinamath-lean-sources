import Mathlib

theorem number_theory_2586 :
    ¬∃ n : ℤ, 49 ∣ n^2 + 3 * n + 4 := by
  rintro ⟨n, hn⟩
  have h1 : (n % 7 = 2) := by
    have h11 : (n ^ 2 + 3 * n + 4) % 7 = 0 := by
      omega
    have h1' : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
      omega
    rcases h1' with (h2 | h2 | h2 | h2 | h2 | h2 | h2) <;> simp [h2, pow_two, Int.add_emod, Int.sub_emod, Int.mul_emod] at h11
    <;> omega
  have h7 : ∃ t : ℤ, n = 7 * t + 2 := by 
    have : n % 7 = 2 := h1
    refine' ⟨n / 7, by omega⟩
  rcases h7 with ⟨t, ht⟩
  rw [ht] at hn
  have h8 : 49 ∣ (7 * t + 2) ^ 2 + 3 * (7 * t + 2) + 4 := by 
    simpa using hn
  have h9 : (7 * t + 2) ^ 2 + 3 * (7 * t + 2) + 4 = 49 * (t^2 + t) + 14 := by 
    ring_nf
  rw [h9] at h8 
  omega