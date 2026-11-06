import Mathlib
open Finset Set Nat
noncomputable section

theorem number_theory_637152 (X : ℕ) (hX : X ≥ 1) :
    (∀ i : Fin 5, (fun j : Fin 5 => (X - 1) * 2^j.val + 1) i > ∑ j ∈ Finset.range i.val,
    (fun j : Fin 5 => (X - 1) * 2^j.val + 1) j) ↔ X ≥ 5 := by
  -- Define the sequence function.
  let s : Fin 5 → ℕ := fun j => (X - 1) * 2^j.val + 1

  -- Verify that $s_i$ is a natural number.
  have h_natural : ∀ i : Fin 5, s i > 0 := by
    intro i
    simp [s]

  -- Compute the sum of previous terms $S_{i-1} = ∑_{j=0}^{i-1} s_j = (X-1)(2^i - 1) + i$.
  have h_sum : ∀ i : Fin 5, ∑ j ∈ Finset.range i.val, s j = (X - 1) * (2^i.val - 1) + i.val := by
    intro i
    have h_sum_split : ∑ j ∈ Finset.range i.val, s j = (X - 1) * ∑ j ∈ Finset.range i.val, 2^j + ∑ j ∈ Finset.range i.val, 1 := by
      calc
      ∑ j ∈ Finset.range i.val, s j
      = ∑ j ∈ Finset.range i.val, ((X - 1) * 2^j + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        unfold s
        have h_j_lt_5 : j < 5 := Nat.lt_trans (Finset.mem_range.mp hj) (Fin.is_lt i)
        simp [h_j_lt_5]
      _ = ∑ j ∈ Finset.range i.val, (X - 1) * 2^j + ∑ j ∈ Finset.range i.val, 1 := Finset.sum_add_distrib
      _ = (X - 1) * ∑ j ∈ Finset.range i.val, 2^j + ∑ j ∈ Finset.range i.val, 1 := by rw [Finset.mul_sum]
    have h_geom_sum : ∑ j ∈ Finset.range i.val, 2^j = 2^i.val - 1 := by
      have : 2^i.val - 1 = (2^i.val - 1)/(2 - 1) := by norm_num
      rw [this]
      exact Nat.geomSum_eq (by nlinarith) i
    have h_one_sum : ∑ j ∈ Finset.range i.val, 1 = i.val := by
      rw [Finset.sum_const]
      simp [Finset.card_range]
    rw [h_sum_split, h_geom_sum, h_one_sum]

  -- Derive the super-increasing condition $s_i > S_{i-1}$ equivalent to $X > i$.
  have h_condition : ∀ i : Fin 5, s i > ∑ j ∈ Finset.range i.val, s j ↔ X > i.val := by
    intro i
    have h_si : s i = (X - 1) * 2^i.val + 1 := by simp [s]
    have h_diff : s i - ∑ j ∈ Finset.range i.val, s j = X - i.val := by
      rw [h_si, h_sum]
      rw [Nat.mul_sub]
      simp [mul_one]
      rw [← Nat.sub_sub]
      have h_sub_cancel : (X - 1) ≤ (X - 1) * 2^i.val := by
        have h_ge_one: 2^i.val ≥ 1 := by exact one_le_pow₀ (by norm_num)
        have : (X - 1) = (X - 1) * 1 := by simp
        conv =>
          left ;rw [this]
        exact Nat.mul_le_mul_left (X - 1) h_ge_one
      omega
    have h_ineq : s i - ∑ j ∈ Finset.range i.val, s j > 0 ↔ X - i.val > 0 := by
      rw [h_diff]
    omega

  -- Determine the condition for all $i$, concluding $X ≥ 5$.
  have h_X_ge_5_necessary : (∀ i : Fin 5, s i > ∑ j ∈ Finset.range i.val, s j) → X ≥ 5 := by
    intro h_super
    have h_i4 : s ⟨4, by norm_num⟩ > ∑ j ∈ Finset.range 4, s j := h_super ⟨4, by norm_num⟩
    have h_X_gt_4 : X > 4 := (h_condition ⟨4, by norm_num⟩).mp h_i4
    linarith

  -- Prove that $X ≥ 5$ is sufficient, completing the bidirectional equivalence.
  have h_X_ge_5_sufficient : X ≥ 5 → (∀ i : Fin 5, s i > ∑ j ∈ Finset.range i.val, s j) := by
    intro h_X
    intro i
    apply (h_condition i).mpr
    apply Nat.lt_of_le_of_lt _ h_X
    simp [Fin.is_le]

  -- Complete the bidirectional proof.
  constructor
  · exact h_X_ge_5_necessary
  · exact h_X_ge_5_sufficient
