import Mathlib

theorem algebra_107284 {n : ℕ} (hn : n ≥ 3) (h : ∃ d, ∀ k ∈ Finset.range n, (k * 180 + 132) = (n - 2) * 180 + d * k) :
    n = 40 := by
  rcases h with ⟨d, hd⟩
  have h0 := hd 0 (Finset.mem_range.mpr (show (0 : ℕ) < n by linarith))
  have h1 := hd 1 (Finset.mem_range.mpr (show (1 : ℕ) < n by linarith))
  have h2 := hd 2 (Finset.mem_range.mpr (show (2 : ℕ) < n by linarith))
  simp at h0 h1 h2
  omega