import Mathlib

def A (r s : ℤ) (n : ℕ) : ℤ := match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => r * A r s (n + 1) + s * A r s n

def f (r s : ℤ) (n : ℕ) : ℤ := ∏ i ∈ Finset.Icc 1 n, A r s i

theorem algebra_8103
  (r s : ℤ)
  (hr : 0 < r)
  (hs : 0 < s)
  (n k : ℕ)
  (hn : 0 < n)
  (hk : 0 < k)
  (hkn : k < n) :
  ∃ m : ℤ, f r s n / (f r s k * f r s (n - k)) = m := by 
  refine ⟨f r s n / (f r s k * f r s (n - k)), rfl⟩