import Mathlib

open Finset

theorem inequalities_62067 {a : ℕ → ℕ} (ha : ∀ n, a n ≤ a (n + 1))
    (haub : ∃ N, ∀ n, a n > N) (ha0 : a 0 = 0) (b : ℕ → ℕ)
    (hb : ∀ n, b n = {i | a i ≤ n}.ncard) (m n : ℕ) :
    (∑ i ∈ range (m + 1), a i) * (∑ i ∈ range (n + 1), b i) ≥
    (m + 1) * (n + 1) := by
  obtain ⟨N, hN⟩ := haub
  have h1 : a 0 > N := hN 0
  have h2 : a 0 ≤ 0 := by
    -- Since 0 = a 0, from ha0
    rw [ha0]
    all_goals omega
  -- Contradicts, since a0 > N contradicts a0 <= 0.
  -- Contradicts since we have h a0 > 0 which can't hold with a0 <= 0.
  omega