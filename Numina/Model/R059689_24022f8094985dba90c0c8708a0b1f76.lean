import Mathlib

def f (n k : ℕ) := n / k + n % k

theorem number_theory_2982 :
    ∑ᶠ k ∈ {k | f 2022 k = 507}, k = 2026 := by
  have h1 : {k | f 2022 k = 507} = {4, 506, 1516} := by
    ext k
    simp [f]
    constructor
    · -- If f 2022 k = 507, then k ∈ {4, 506, 1516}
      intro h
      have h1 : k ≤ 2022 := by
        by_contra h2
        push_neg at h2
        have h2 : k > 2022 := h2
        have h2 : 2022 / k = 0 := by
          rw [Nat.div_eq_zero_iff]
          omega
        have h2 : 2022 % k = 2022 := by
          rw [Nat.mod_eq_of_lt]
          omega
          all_goals nlinarith
        omega
      interval_cases k <;> norm_num at h ⊢ <;> try { tauto }
      all_goals try { omega }
      all_goals try { norm_num at h }
    · -- If k ∈ {4, 506, 1516}, then f 2022 k = 507
      rintro (rfl | rfl | rfl)
      · -- k = 4
        norm_num [f]
      · -- k = 506
        norm_num [f]
      · -- k = 1516
        norm_num [f]
  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num
  all_goals try { simp }
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { simp }
  all_goals norm_num
  all_goals try { tauto }
  all_goals norm_num
  all_goals try { tauto }