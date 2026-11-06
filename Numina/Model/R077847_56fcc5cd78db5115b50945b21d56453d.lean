import Mathlib

theorem number_theory_104396 (S : Finset ℤ) (hS : S.card = 40)
    (hS1 : ∀ x ∈ S, ¬ 5 ∣ x) :
    5 ∣ ∑ x ∈ S, x^4 := by 
  have h1 : ∀ x ∈ S, x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by
    intro x hx
    have h2 : ¬ 5 ∣ x := hS1 x hx
    omega
  have h2 : ∀ x ∈ S, (x ^ 4) % 5 = 1 := by 
    intro x hx
    rcases h1 x hx with h | h | h | h <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    <;> omega
  have h3 : (∑ x in S, x ^ 4) % 5 = 0 := by
    have h4 : ∀ x ∈ S, (x ^ 4) % 5 = 1 := h2
    have h5 : (∑ x in S, x ^ 4) % 5 = (∑ x in S, (x ^ 4) % 5) % 5 := by
      simp [Finset.sum_int_mod]
    rw [h5]
    have h6 : ∑ x in S, (x ^ 4) % 5 = 40 := by
      have h8 : ∀ x ∈ S, (x ^ 4) % 5 = 1 := h2
      have h9 : ∑ x in S, (x ^ 4) % 5 = ∑ x in S, (1 : ℤ) := by
        apply Finset.sum_congr
        · rfl
        intro x hx
        exact h8 x hx
      rw [h9]
      simp [hS]
      <;> try { omega }
      <;> try linarith
      <;> try { native_decide }
    rw [h6]
    all_goals omega
    all_goals try native_decide
  exact Int.dvd_of_emod_eq_zero h3