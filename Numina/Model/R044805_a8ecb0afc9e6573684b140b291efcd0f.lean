import Mathlib

theorem number_theory_219388 (a d : ℤ) (n : ℕ) (h₀ : n > 0) (h₁ : Even n) :
    ∑ i ∈ Finset.range (n / 2), (a + d * (n / 2 + i)) - ∑ i ∈ Finset.range (n / 2), (a + d * i) ≡
    0 [ZMOD (n / 2) ^ 2] := by
  have h2 : n % 2 = 0 := by
    obtain ⟨k, hk⟩ := h₁
    omega
  have h3 : ∑ i in Finset.range (n / 2), (a + d * (n / 2 + i)) - ∑ i in Finset.range (n / 2), (a + d * i) = d * ((n / 2 : ℤ) )^2 := by
    have h4 : ∑ i in Finset.range (n / 2), (a + d * (n / 2 + i)) - ∑ i in Finset.range (n / 2), (a + d * i) =
        ∑ i in Finset.range (n / 2), ((a + d * (n / 2 + i)) - (a + d * i)) := by
      rw [Finset.sum_sub_distrib]
    rw [h4]
    have h5 : ∑ i in Finset.range (n / 2), ((a + d * (n / 2 + i)) - (a + d * i)) = d * ((n / 2 : ℤ) )^2 := by
      have h6 : ∀ i : ℕ, ((a + d * ((n / 2 : ℤ) + (i : ℤ))) - (a + d * (i : ℤ)) ) = d * (n / 2 : ℤ) := by
        intro i
        simp [add_mul, mul_add, sub_eq_add_neg]
        all_goals ring
      have h7 : ∑ i in Finset.range (n / 2), ((a + d * (n / 2 + i)) - (a + d * i)) = ∑ i in Finset.range (n / 2), (d * ((n / 2 : ℤ) ) ) := by
        apply Finset.sum_congr
        · rfl
        · intro i hi
          specialize h6 i
          simpa using h6
      rw [h7]
      have h8 : ∑ i in Finset.range (n / 2), (d * ((n / 2 : ℤ) ) ) = d * ((n / 2 : ℤ) )^2 := by
        simp [Finset.sum_const, mul_add, mul_assoc]
        all_goals
          ring
      exact h8
    exact h5
  rw [h3]
  have h9 : ((d * ((n / 2 : ℤ) )^2) : ℤ) % ((n / 2 : ℤ) ^ 2 : ℤ) = 0 := by
    have h10 : ((n / 2 : ℤ) ^ 2 : ℤ) ∣ (d * ((n / 2 : ℤ) ) ^ 2 : ℤ) := by
      use d
      all_goals ring
    have h11 : ((d * ((n / 2 : ℤ) ) ^ 2 : ℤ) : ℤ) % ((n / 2 : ℤ) ^ 2 : ℤ) = 0 := by
      have h100 : ((n / 2 : ℤ) ^ 2 : ℤ) ∣ (d * ((n / 2 : ℤ) ) ^ 2 : ℤ) := h10
      exact Int.emod_eq_zero_of_dvd h100
    exact h11
  simp [Int.ModEq] at *
  all_goals
    omega