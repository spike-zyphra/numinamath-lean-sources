import Mathlib

theorem number_theory_6585 (f : ℕ → ℕ) (hf : ∀ n, f n = ∑ i ∈ Finset.range n, 10 ^ i) :
    (∑ n ∈ Finset.Icc 1 2021, (n * f n)) % 1000 = 331 := by
  rw [Finset.sum_congr rfl (fun n _ => by rw [hf n])]
  native_decide