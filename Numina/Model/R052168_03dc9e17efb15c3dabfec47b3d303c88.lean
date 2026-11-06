import Mathlib

theorem algebra_230654 (n : ℕ) (hn : n > 0) (a : Fin n → ℤ)
    (ha : ∑ i : Fin n, a i = 22) (b : Fin n → ℤ)
    (hb : ∀ i : Fin n, b i = 7 - a i) (hsum : ∑ i : Fin n, b i = 34) :
    n = 8 := by
  have h1 : ∀ i : Fin n, b i = 7 - a i := hb
  have eq1 : ∑ i : Fin n, b i = ∑ i : Fin n, (7 - a i) := by
    apply Finset.sum_congr
    · rfl 
    · intro i hi
      specialize h1 i
      linarith [h1]
  rw [eq1] at hsum
  have h2 : ∑ i : Fin n, (7 - a i) = 7 * (n : ℤ) - ∑ i : Fin n, a i := by 
    have h3 : ∑ i : Fin n, (7 - a i) = ∑ i : Fin n, (7 : ℤ) - ∑ i : Fin n, (a i) := by 
      simp [Finset.sum_sub_distrib]
    rw [h3]
    have h4 : ∑ i : Fin n, (7 : ℤ) = (n : ℤ) * 7 := by
      simp [Finset.sum_const, mul_comm]
      <;> ring
      <;> omega
    rw [h4]
    all_goals omega
  rw [h2] at hsum
  rw [ha] at hsum
  have hn8 : (n : ℤ) = 8 := by
    omega
  exact_mod_cast hn8