import Mathlib

theorem algebra_1591 (a : ℕ → ℤ) (ha : a 0 = -44) (ha' : ∀ i, a (i + 1) = a i + 1) :
    ∑ i ∈ Finset.range 100, a i = 550 := by 
  have h1 : ∀ i, a i = -44 + (i : ℤ) := by 
    intro i
    induction i with
    | zero =>
      simp [ha]
    | succ i ih =>
      simp [ha', ih]
      <;> ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  norm_num [Finset.sum_range_succ]