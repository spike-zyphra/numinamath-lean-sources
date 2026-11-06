import Mathlib

theorem number_theory_237789 (N : ℕ) :
    (∃ k, N ≥ 3 ∧ k > 0 ∧ (N - k) % 6 = 0) ↔ N ≥ 3 := by 
  constructor
  · -- Forward: If there exists k such that N ≥ 3, k > 0, and (N - k) ≡ 0 (mod 6), then N ≥ 3
    rintro ⟨k, hN, hk, hdiv⟩
    exact hN
  · -- Backward: If N ≥ 3, then there exists k such that k > 0 and (N - k) ≡ 0 (mod 6)
    intro hN
    have h1 : N % 6 = 0 ∨ N % 6 = 1 ∨ N % 6 = 2 ∨ N % 6 = 3 ∨ N % 6 = 4 ∨ N % 6 = 5 := by 
      omega
    rcases h1 with (h1 | h1 | h1 | h1 | h1 | h1)
    · -- Case N % 6 = 0
      have h2 : (N : ℕ) % 6 = 0 := h1
      use 6
      constructor
      · omega
      constructor
      · norm_num
      · -- Show (N - 6) % 6 = 0
        omega
    · -- Case N % 6 = 1
      have h2 : (N : ℕ) % 6 = 1 := h1
      use 1
      constructor
      · omega
      constructor
      · norm_num
      · -- Show (N - 1) % 6 = 0
        omega
    · -- Case N % 6 = 2
      have h2 : (N : ℕ) % 6 = 2 := h1
      use 2
      constructor
      · omega
      constructor
      · norm_num
      · -- Show (N - 2) % 6 = 0
        omega
    · -- Case N % 6 = 3
      have h2 : (N : ℕ) % 6 = 3 := h1
      use 3
      constructor
      · omega
      constructor
      · norm_num
      · -- Show (N - 3) % 6 = 0
        omega
    · -- Case N % 6 = 4
      have h2 : (N : ℕ) % 6 = 4 := h1
      use 4
      constructor
      · omega
      constructor
      · norm_num
      · -- Show (N - 4) % 6 = 0
        omega
    · -- Case N % 6 = 5
      have h2 : (N : ℕ) % 6 = 5 := h1
      use 5
      constructor
      · omega
      constructor
      · norm_num
      · -- Show (N - 5) % 6 = 0
        omega