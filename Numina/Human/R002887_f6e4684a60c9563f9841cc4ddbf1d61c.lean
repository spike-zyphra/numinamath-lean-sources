import Mathlib
open Finset Set Nat 
noncomputable section

/-
Problem 1. Suppose $r \geq 2$ is an integer, and let $m_{1}, n_{1}, m_{2}, n_{2}, \cdots, m_{r}, n_{r}$ be $2 r$ integers such that
$$
\left|m_{i} n_{j}-m_{j} n_{i}\right|=1
$$
for any two integers $i$ and $j$ satisfying $1 \leq i<j \leq r$. Determine the maximum possible value of $r$.
-/
theorem number_theory_606666 :
    (∀ r : ℕ, r ≥ 4 → ∃ m n : Fin r → ℤ,
        ∃ i j : Fin r, i < j ∧ |m i * n j - m j * n i| ≠ 1) ∧
    (∃ m n : Fin 3 → ℤ,
        ∀ i j : Fin 3, i < j → |m i * n j - m j * n i| = 1) := by
  have h_r_ge_4_impossible : ∀ r : ℕ, r ≥ 4 → ∃ m n : Fin r → ℤ, ∃ i j : Fin r, i < j ∧ |m i * n j - m j * n i| ≠ 1 := by
    intro r hr
    have h_construct_counterexample : ∃ m n : Fin r → ℤ, ∃ i j : Fin r, i < j ∧ |m i * n j - m j * n i| ≠ 1 := by
      -- Construct m = n = 0 to find i, j where |m_i n_j - m_j n_i| ≠ 1
      use fun _ => 0, fun _ => 0
      use ⟨0, by omega⟩, ⟨1, by omega⟩
      constructor
      · simp [Fin.ext_iff]
      · simp [abs_eq_max_neg]
    exact h_construct_counterexample
  have h_r_eq_3_possible : ∃ m n : Fin 3 → ℤ, ∀ i j : Fin 3, i < j → |m i * n j - m j * n i| = 1 := by
    -- Construct m, n for r = 3 to satisfy |m_i n_j - m_j n_i| = 1 for all i < j
    use fun i => match i with
      | ⟨0, _⟩ => 1
      | ⟨1, _⟩ => 1
      | ⟨2, _⟩ => 2
      | ⟨n + 3, _⟩ => by exfalso; omega
    use fun i => match i with
      | ⟨0, _⟩ => 0
      | ⟨1, _⟩ => 1
      | ⟨2, _⟩ => 1
      | ⟨n + 3, _⟩ => by exfalso; omega
    intro i j hij
    -- Verify condition for i < j, handle i ≥ j by contradiction
    fin_cases i <;> fin_cases j
    · exfalso; simp at hij
    · norm_num
    · norm_num
    · exfalso; simp at hij
    · exfalso; simp at hij
    · norm_num
    · exfalso; simp at hij
    · exfalso; simp at hij
    · exfalso; simp at hij
  exact ⟨h_r_ge_4_impossible, h_r_eq_3_possible⟩