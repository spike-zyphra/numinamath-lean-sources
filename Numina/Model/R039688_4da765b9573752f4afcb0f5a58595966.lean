import Mathlib

theorem algebra_13400 {secret_known : ℕ → ℕ} (h : ∀ n, secret_known n = ∑ i ∈ Finset.range (n + 1), 2 ^ i) :
secret_known m = 1023 → m % 7 = 2 := by
  intro h1
  have eq1 : ∀ n, secret_known n = 2 ^ (n + 1) - 1 := by
    intro n
    rw [h n]
    induction n with
    | zero => 
      simp [Finset.sum_range_succ]
      <;> omega
    | succ n ih => 
      simp [Finset.sum_range_succ, ih]
      <;> ring_nf
      <;> omega
  have eq2 : secret_known m = 2 ^ (m + 1) - 1 := eq1 m
  rw [eq2] at h1
  have h2 : 2 ^ (m + 1) = 1024 := by
    omega
  have h3 : m + 1 = 10 := by
    exact Nat.pow_right_injective (by norm_num) h2
  have h4 : m = 9 := by
    omega
  calc
    m % 7 = 9 % 7 := by rw [h4]
    _ = 2 := by norm_num