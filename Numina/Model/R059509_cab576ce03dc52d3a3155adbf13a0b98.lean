import Mathlib

theorem algebra_244774 (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (a : ℕ → ℤ) (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = r * a (n - 1) + s * a (n - 2))
    (f : ℕ → ℤ) (hf : ∀ n, f n = ∏ i ∈ Finset.Icc 1 n, a i) :
    ∀ n k, 0 < k → k < n → ∃ m, f n / (f k * f (n - k)) = m := by 
  intro n k hk hkn 
  refine' ⟨f n / (f k * f (n - k)), rfl⟩