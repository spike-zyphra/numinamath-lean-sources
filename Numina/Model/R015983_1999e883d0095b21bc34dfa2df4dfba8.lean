import Mathlib

theorem number_theory_37213 (n : ℤ) (hn : n > 0) :
    13 ∣ n^2 + 3 * n + 51 → 169 ∣ 21 * n^2 + 89 * n + 44 := by 
  intro h
  have h1 : n % 13 = 5 := by
    have h3 : (n ^ 2 + 3 * n + 51) % 13 = 0 := by
      omega 
    have h4 : n % 13 = 0 ∨ n % 13 = 1 ∨ n % 13 = 2 ∨ n % 13 = 3 ∨ n % 13 = 4 ∨ n % 13 = 5 ∨ n % 13 = 6 ∨ n % 13 = 7 ∨ n % 13 = 8 ∨ n % 13 = 9 ∨ n % 13 = 10 ∨ n % 13 = 11 ∨ n % 13 = 12 := by
      omega 
    rcases h4 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h] at h3 <;> try { tauto }
  have h2 : ∃ k : ℤ, n = 13 * k + 5 := by
    refine' ⟨(n - 5) / 13, by 
      omega 
    ⟩
  rcases h2 with ⟨k, hk⟩
  have h3 : 21 * n^2 + 89 * n + 44 = 169 * (21 * k^2 + 23 * k + 6) := by
    rw [hk]
    ring
  rw [h3]
  use 21 * k^2 + 23 * k + 6
  all_goals ring