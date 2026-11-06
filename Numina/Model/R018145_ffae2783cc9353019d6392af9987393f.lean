import Mathlib

def M : Set ℚ := {x | ∃ n : ℤ, x = n}
def N : Set ℚ := {x | ∃ n : ℤ, x = n / 2}
def P : Set ℚ := {x | ∃ n : ℤ, x = n + 1 / 2}

theorem number_theory_171471 : N = M ∪ P := by
  ext x
  simp only [N, M, P, Set.mem_union]
  constructor
  · -- Assume x ∈ N, need to show x ∈ M ∪ P
    rintro ⟨n, hn⟩
    by_cases h : (n : ℤ) % 2 = 0
    · -- If n is even, then n = 2k, so n/2 = k
      have h1 : ∃ k : ℤ, n = 2 * k := by
        refine' ⟨n / 2, by omega⟩
      rcases h1 with ⟨k, hk⟩
      have h2 : (x : ℚ) = (k : ℚ) := by
        rw [hn]
        rw [hk]
        norm_num
        <;> ring_nf
      left
      exact ⟨k, by linarith⟩
    · -- If n is odd, then n = 2k + 1, so n/2 = k + 1/2
      have h2 : (n : ℤ) % 2 = 1 := by omega
      have h1 : ∃ k : ℤ, n = 2 * k + 1 := by 
        have h3 : (n : ℤ) % 2 = 1 := h2
        have h4 : ∃ k, n = 2 * k + 1 := by 
          refine' ⟨(n - 1) / 2, by omega⟩
        exact h4
      rcases h1 with ⟨k, hk⟩
      have h3 : (x : ℚ) = (k : ℚ) + (1 / 2) := by
        rw [hn]
        rw [hk]
        field_simp
        <;> ring_nf
      right
      exact ⟨k, by linarith⟩
  · -- Assume x ∈ M ∪ P, need to show x ∈ N
    rintro (h | h)
    · -- Case where x ∈ M
      rcases h with ⟨n, hn⟩
      refine' ⟨2 * n, by
        rw [hn]
        field_simp
        <;> ring_nf
      ⟩
    · -- Case where x ∈ P
      rcases h with ⟨n, hn⟩
      refine' ⟨2 * n + 1, by
        rw [hn]
        field_simp
        <;> ring_nf
      ⟩