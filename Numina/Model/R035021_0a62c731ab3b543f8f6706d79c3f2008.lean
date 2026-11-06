import Mathlib

open Int

theorem number_theory_7473 :
    IsLeast {n | ∃ x : Fin n → ℤ, ∑ i : Fin n, (x i)^4 = 1599} 15 := by
  constructor
  · -- Show 15 is in the set
    use fun i =>
      if i = 0 then 5
      else if i = 1 then 3
      else if i = 2 then 3
      else if i = 3 then 3
      else if i = 4 then 3
      else if i = 5 then 3
      else if i = 6 then 3
      else if i = 7 then 3
      else if i = 8 then 3
      else if i = 9 then 3
      else if i = 10 then 3
      else if i = 11 then 3
      else if i = 12 then 3
      else if i = 13 then 1
      else if i = 14 then 1
      else 0
    native_decide
  · -- Show no smaller n is in the set
    intro n hn
    rcases hn with ⟨x, hx⟩
    by_contra h
    push_neg at h
    have h1 : n < 15 := by
      omega
    have h2 : ∑ i : Fin n, (x i)^4 = 1599 := hx
    have h3 : n ≤ 14 := by
      omega
    have h1 : ∀ i : Fin n, (x i) ^ 4 % 16 = 0 ∨ (x i) ^ 4 % 16 = 1 := by
      intro i
      have h11 : (x i) % 16 = 0 ∨ (x i) % 16 = 1 ∨ (x i) % 16 = 2 ∨ (x i) % 16 = 3 ∨ (x i) % 16 = 4 ∨ (x i) % 16 = 5 ∨ (x i) % 16 = 6 ∨ (x i) % 16 = 7 ∨ (x i) % 16 = 8 ∨ (x i) % 16 = 9 ∨ (x i) % 16 = 10 ∨ (x i) % 16 = 11 ∨ (x i) % 16 = 12 ∨ (x i) % 16 = 13 ∨ (x i) % 16 = 14 ∨ (x i) % 16 = 15 := by
        omega
      rcases h11 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h3 : (∑ i : Fin n, (x i) ^ 4) % 16 ≤ (n : ℤ) := by
      have h4 : (∑ i : Fin n, (x i) ^ 4) % 16 = (∑ i : Fin n, ((x i) ^ 4 % 16)) % 16 := by
        simp [Finset.sum_int_mod]
      rw [h4]
      have h6 : (∑ i : Fin n, ((x i) ^ 4 % 16)) ≤ (n : ℤ) := by
        have h7 : ∀ i : Fin n, ((x i) ^ 4 % 16) ≤ 1 := by
          intro i
          have h8 : ((x i) ^ 4 % 16 = 0 ∨ (x i) ^ 4 % 16 = 1) := h1 i
          omega
        have h9 : (∑ i : Fin n, ((x i) ^ 4 % 16)) ≤ ∑ i : Fin n, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact h7 i
        have h10 : ∑ i : Fin n, (1 : ℤ) = (↑n : ℤ) := by
          simp
        linarith [h9, h10]
      have h7 : (∑ i : Fin n, ((x i) ^ 4 % 16)) ≥ 0 := by
        apply Finset.sum_nonneg
        intro i hi
        omega
      omega
    have h8 : (1599 : ℤ) % 16 = 15 := by
      omega
    have h9 : (∑ i : Fin n, (x i) ^ 4) % 16 = 15 := by
      omega
    omega