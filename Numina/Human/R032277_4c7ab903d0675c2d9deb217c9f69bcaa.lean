import Mathlib

open Real Set
open scoped Real

/- The solution set of the equation $\sin^2x - 2\sin x = 0$ is. -/
theorem algebra_9077 (x : ℝ) :
  sin x ^ 2 - 2 * sin x = 0 ↔ ∃ k : ℤ, x = k * π := by
  -- Factor the left-hand side of the equivalence
  have h₀ : sin x ^ 2 - 2 * sin x = sin x * (sin x - 2) := by ring
  rw [h₀]
  -- Prove the equivalence using a constructive proof
  constructor
  . -- Prove the forward direction: if sin^2(x) - 2sin(x) = 0, then x = kπ for some integer k
    intro hx
    -- Use the zero product property
    rw [mul_eq_zero] at hx
    rcases hx with hl | hr
    . -- Case 1: sin(x) = 0
      rw [sin_eq_zero_iff] at hl
      obtain ⟨hn, hnx⟩ := hl
      rw [eq_comm] at hnx
      exact ⟨hn, hnx⟩
    . -- Case 2: sin(x) - 2 = 0
      have hf : sin x = 2 := by
        calc
          sin x = sin x - 2 + 2 := by norm_num
            _ = 0 + 2 := by rw [hr]
            _ = 2 := by norm_num
      have h₀ : sin x ≤ 1 := sin_le_one x
      rw [hf] at h₀
      have h₁ : False := by linarith
      exact False.elim h₁
  . -- Prove the backward direction: if x = kπ for some integer k, then sin^2(x) - 2sin(x) = 0
    intro ⟨k, hk⟩
    rw [eq_comm] at hk
    have h₁ : ∃ n : ℤ, ↑n * π = x := ⟨k, hk⟩
    rw [← sin_eq_zero_iff] at h₁
    rw [h₁, zero_mul]
