import Mathlib
open Finset Nat Classical
set_option maxRecDepth 20000
noncomputable section

-- Define a predicate for $(m, N)$ where $N$ consecutive positive integers from m sum to $75$.
def is_consecutive_sum_to_75 (p : ℕ × ℕ) : Prop :=
  let m := p.fst
  let N := p.snd
  m > 0 ∧ N ≥ 2 ∧ (∑ k ∈ Finset.range N, (m + k)) = 75

/-In how many ways can 75 be expressed as the sum of two or more consecutive positive integers?
(A) 1
(B) 2
(C) 3
(D) 4
(E) 5-/
theorem number_theory_6012123 : Finset.card (Finset.filter (λ p : ℕ × ℕ => is_consecutive_sum_to_75 p)
  (Finset.product (Finset.range 75 |>.image (λ k => k + 1)) (Finset.range 75 |>.image (λ k => k + 2)))) = 5 := by
  have h_filter_eq_pairs : Finset.filter (λ p : ℕ × ℕ => is_consecutive_sum_to_75 p) (Finset.product (Finset.range 75 |>.image (λ k => k + 1)) (Finset.range 75 |>.image (λ k => k + 2))) = {(37, 2), (24, 3), (13, 5), (10, 6), (3, 10)} := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_range, Finset.mem_singleton,
      is_consecutive_sum_to_75, Prod.mk.injEq]
    constructor
    · -- Forward direction: if $p$ is in the filtered set, then $p$ is one of the five pairs.
      intro h
      rcases p with ⟨m, N⟩
      simp at h ⊢
      -- Extract conditions from $h$.
      have h_m_positive : m > 0 := by omega
      have h_N_at_least_2 : N ≥ 2 := by omega
      have h_sum_75 : (∑ k ∈ Finset.range N, (m + k)) = 75 := by omega
      -- Prove $N ≤ 12$.
      have h_N_le_12 : N ≤ 12 := by
        by_contra h_contra
        have h_N_ge_13 : N ≥ 13 := by nlinarith
        have h_sum_m_ge_1 : ∑ k ∈ Finset.range N, (m + k) ≥ ∑ k ∈ Finset.range N, (1 + k) := by
          apply Finset.sum_le_sum
          intro k _; omega
        have h_sum_1_ge_78 : ∑ k ∈ Finset.range N, (1 + k) ≥ 78 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Finset.sum_range_id]
          simp
          have : N * (N - 1) / 2 ≥ 12 * 11 / 2 := by
            apply Nat.div_le_div_right
            apply Nat.mul_le_mul
            · nlinarith
            · omega
          norm_num at this
          linarith
        have : ∑ k ∈ Finset.range N, (m + k) ≥ 78 := Nat.le_trans h_sum_1_ge_78 h_sum_m_ge_1
        rw [h_sum_75] at this
        linarith
      -- Check possible $N$ values.
      have h_N_cases : N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 ∨ N = 9 ∨ N = 10 ∨ N = 11 ∨ N = 12 := by
        omega
      rcases h_N_cases with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · have h_m_eq_37 : m = 37 := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_eq_24 : m = 24 := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_invalid : False := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_eq_13 : m = 13 := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_eq_10 : m = 10 := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_invalid : False := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_invalid : False := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_invalid : False := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_eq_3 : m = 3 := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_invalid : False := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
      · have h_m_invalid : False := by
          simp [Finset.sum_range_succ] at h_sum_75
          omega
        simp_all
    · -- Reverse direction: if $p$ is one of the five pairs, then $p$ is in the filtered set.
      intro h
      rcases p with ⟨m, N⟩
      simp at h ⊢
      -- Check each of the five pairs to see if they satisfy the conditions.
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Case $(37, 2)$.
        simp [is_consecutive_sum_to_75, Finset.sum_range_succ]
        decide
      · -- Case $(24, 3)$.
        simp [is_consecutive_sum_to_75, Finset.sum_range_succ]
        decide
      · -- Case $(13, 5)$.
        simp [is_consecutive_sum_to_75, Finset.sum_range_succ]
        decide
      · -- Case $(10, 6)$.
        simp [is_consecutive_sum_to_75, Finset.sum_range_succ]
        decide
      · -- Case $(3, 10)$.
        simp [is_consecutive_sum_to_75, Finset.sum_range_succ]
        decide
  rw [h_filter_eq_pairs]
  simp
