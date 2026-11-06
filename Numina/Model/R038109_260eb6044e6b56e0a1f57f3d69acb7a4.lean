import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_162018 {f : ℝ → ℝ} (hf : f = λ x => x + 1 / x)
  (M N : ℝ) (hMN : M > 0 ∧ N > 0) (hMN1 : M ≠ N)
  (hM : f M = 1 + k * M) (hN : f N = 1 + k * N) :
  (k * 2 + 1, k * 2 + 5 / 2) ∈ {(x, y) | ∃ M N : ℝ, M > 0 ∧ N > 0 ∧ M ≠ N ∧ f M = 1 + k * M ∧ f N = 1 + k * N} := by
    exact ⟨M, N, hMN.1, hMN.2, hMN1, hM, hN⟩