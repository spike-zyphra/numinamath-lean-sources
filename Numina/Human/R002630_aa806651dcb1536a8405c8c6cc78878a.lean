import Mathlib
/-- Find the sum of all positive integers $n$ for which $n^2-19n+99$ is a perfect square. -/
theorem number_theory_97145 :
∑ᶠ n ∈ {n : ℕ | 0 < n ∧ ∃ k, k^2 = (↑n^2 : ℤ) - 19 * n + 99}, n = 38 := by
  -- list all divisors
  have ta {a b : ℤ} (h : a * b = 35) :
      a = -35 ∨ a = -7 ∨ a = -5 ∨ a = -1 ∨ a = 1 ∨ a = 5 ∨ a = 7 ∨ a = 35 := by
    have ha : a.natAbs ∈ (35).divisors := by
      simp; use b.natAbs; rw [←Int.natAbs_mul, h]; rfl
    simp only [show (35 : ℕ).divisors = { 1, 5, 7, 35 } from rfl, Finset.mem_insert,
      Finset.mem_singleton] at ha
    omega
  have enum : {n : ℕ | 0 < n ∧ ∃ k, k^2 = (↑n^2 : ℤ) - 19 * n + 99} = ↑({1, 9, 10, 18} : Finset ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor <;> intro h
    · obtain ⟨a, k, s⟩ := h
      -- have something to factor
      have wkw : (2 * k - 2 * n + 19) * (2 * k + 2 * n - 19) = 35 := by ring_nf; linarith
      obtain ald | ald | ald | ald | ald | ald | ald | ald := ta wkw
      all_goals zify at *
      all_goals rw [ald] at wkw
      all_goals omega
    · obtain rfl | rfl | rfl | rfl := h
      all_goals norm_num
      exists 9; exists 3; exists 3; exists 9
  -- calculate sum
  rw [enum, finsum_mem_coe_finset]
  decide