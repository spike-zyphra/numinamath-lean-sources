import Mathlib

open List Finset

theorem algebra_94715 {n : ℕ} {a : Fin n → ℤ} (h1 : ∑ i, (a i + 3) = 45) (h2 : ∑ i, 3 * a i = 45) :
n = 10 := by 
  have eq1 : ∑ i : Fin n, (a i + 3) = (∑ i : Fin n, a i) + 3 * (n : ℤ) := by
    have h3 : ∑ i : Fin n, (a i + 3) = (∑ i : Fin n, a i) + (∑ i : Fin n, (3 : ℤ)) := by
      rw [Finset.sum_add_distrib]
    rw [h3]
    have h4 : (∑ i : Fin n, (3 : ℤ)) = 3 * (n : ℤ) := by 
      simp [Finset.sum_const, Finset.card_univ]
      <;> ring 
    rw [h4]
  have eq2 : (∑ i : Fin n, (3 * a i : ℤ)) = 3 * (∑ i : Fin n, (a i : ℤ)) := by
    simp [Finset.mul_sum]
  rw [eq1] at h1
  rw [eq2] at h2 
  have eq3 : ∑ i : Fin n, (a i : ℤ) = 15 := by 
    linarith 
  have eq5 : (n : ℤ) = 10 := by 
    rw [eq3] at h1 
    linarith 
  have eq7 : n = 10 := by 
    exact_mod_cast eq5 
  exact eq7