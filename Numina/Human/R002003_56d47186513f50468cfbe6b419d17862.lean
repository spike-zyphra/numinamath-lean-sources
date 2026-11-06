import Mathlib
/-- Find the sum of all positive integers $n$ such that $\sqrt{n^2+85n+2017}$ is an integer. -/
theorem algebra_53827 :
∑ᶠ n ∈ {n : ℕ | 0 < n ∧ ∃ k, k^2 = (↑n^2 : ℤ) + 85 * n + 2017}, n = 195 := by
  -- list all divisors
  have ta {a b : ℤ} (h : a * b = 843) :
      a = 1 ∨ a = 3 ∨ a = 281 ∨ a = 843 ∨ a = -1 ∨ a = -3 ∨ a = -281 ∨ a = -843 := by
    have ha : a.natAbs ∈ (843).divisors := by
      simp; use b.natAbs; rw [←Int.natAbs_mul, h]; rfl
    simp only [(by native_decide : (843 : ℕ).divisors = { 1, 3, 281, 843 }), Finset.mem_insert,
      Finset.mem_singleton] at ha
    omega
  have enum : {n : ℕ | 0 < n ∧ ∃ k, k^2 = (↑n^2 : ℤ) + 85 * n + 2017} = ↑({168, 27} : Finset ℕ) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor <;> intro h
    · obtain ⟨a, k, s⟩ := h
      -- have something to factor
      have wkw : (2 * k - 2 * n - 85) * (2 * k + 2 * n + 85) = 843 := by ring_nf; linarith
      obtain ald | ald | ald | ald | ald | ald | ald | ald := ta wkw
      all_goals zify at *
      all_goals rw [ald] at wkw
      all_goals omega
    · obtain rfl | rfl | rfl | rfl := h
      all_goals norm_num
      exists 211
      exists 71
  -- calculate sum
  rw [enum, finsum_mem_coe_finset]
  decide