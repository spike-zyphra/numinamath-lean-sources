import Mathlib

def a (r s : ℕ) (n : ℕ) : ℕ := match n with
| 0 => 0
| 1 => 1
| n + 2 => r * a r s (n + 1) + s * a r s n

def f (r s : ℕ) (n : ℕ) := ∏ i ∈ Finset.Icc 1 n, a r s i

theorem number_theory_67180 (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∀ n k, 0 < k → k < n → ∃ m, f r s n / (f r s k * f r s (n - k)) = m := by
  intro n k hk hkn
  refine' ⟨f r s n / (f r s k * f r s (n - k)), rfl⟩