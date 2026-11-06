import Mathlib

theorem algebra_1719 (t : ℕ → ℚ) (ht : ∀ n, t n = n * (n + 1) / 2) :
    ∑ n in Finset.Icc 1 2002, 1 / t n = 4004 / 2003 := by
  have h1 : ∀ n : ℕ, t n = n * (n + 1) / 2 := ht
  have h2 : ∀ n : ℕ, 1 / t n = 2 / (n * (n + 1) : ℚ) := by
    intro n
    rw [h1 n]
    field_simp
    <;> ring_nf
  rw [Finset.sum_congr rfl (fun n hn => h2 n)]
  native_decide