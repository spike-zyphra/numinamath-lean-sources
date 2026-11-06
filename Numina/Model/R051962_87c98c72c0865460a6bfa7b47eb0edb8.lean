import Mathlib

def is_prime (n : ℕ) : Prop :=
  Nat.Prime n

theorem number_theory_1436 {n : ℕ} (h : is_prime n) (h1 : n ∈ Finset.Icc 10 99) (h2 : n % 10 - (n / 10) = 7) :
    n = 29 := by
  rw [Finset.mem_Icc] at h1
  rcases h1 with ⟨h10, h19⟩
  unfold is_prime at h
  interval_cases n <;> norm_num at h h10 h19 h2 ⊢
  <;> try { contradiction }
  <;> try { trivial }