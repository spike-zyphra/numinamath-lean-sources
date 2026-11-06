import Mathlib

theorem number_theory_193501 (n : ℤ) :
    3 ∣ (5 * n ^ 2 + 10 * n + 8) ↔ ∃ k, n = 2 + 3 * k := by
  constructor
  · -- Assume 3 divides 5 * n ^ 2 + 10 * n + 8, we need to prove ∃ k, n = 2 + 3 * k
    intro h
    have h_n_mod_3 : n % 3 = 2 := by
      have h1 : (5 * n ^ 2 + 10 * n + 8) % 3 = 0 := by
        omega
      have eq1 : (5 * n ^ 2 + 10 * n + 8) % 3 = (2 * (n ^ 2) + n + 2) % 3 := by
        simp [Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.emod_self]
        <;> ring_nf <;> simp [Int.add_emod, Int.mul_emod, pow_two, Int.sub_emod, Int.emod_self]
        <;> omega
      rw [eq1] at h1
      have h_n : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      rcases h_n with (h | h | h)
      · -- n % 3 = 0
        simp [pow_two, h, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1
        all_goals omega
      · -- n % 3 = 1
        simp [pow_two, h, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1
        all_goals omega
      · -- n % 3 = 2
        simp [pow_two, h, Int.add_emod, Int.mul_emod, Int.sub_emod] at h1
        all_goals omega
    have : ∃ k, n = 2 + 3 * k := by
      refine' ⟨(n - 2) / 3, by omega⟩
    rcases this with ⟨k, hk⟩
    exact ⟨k, hk⟩
  · -- Assume ∃ k, n = 2 + 3 * k, we need to prove 3 ∣ (5 * n ^ 2 + 10 * n + 8)
    rintro ⟨k, hk⟩
    rw [hk]
    use (15 * k ^ 2 + 30 * k + 16)
    <;> ring_nf <;> omega