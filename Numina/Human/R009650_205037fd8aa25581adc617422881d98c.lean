import Mathlib

theorem number_theory_75318 (n : ℕ) :
    ¬Nat.Prime (2000 * 10 ^ n + ∑ k ∈ Finset.range n, 8 * 10 ^ (k + 2) + 21) := by
  -- Note that ∑ k ∈ Finset.range n, 10 ^ k = (10 ^ n - 1) / (10 - 1).
  have h₀ := Nat.geomSum_eq (show 2 ≤ 10 by norm_num) n
  -- Note that 10 - 1 ∣ 10 ^ n - 1, and we let N be the quotient.
  have h₁ := sub_one_dvd_pow_sub_one (10 : ℤ) n
  norm_cast at h₁
  -- Verify that 1 ≤ 10 and 1 ≤ 10 ^ n.
  have h₂ : 1 ≤ 10 ^ n := by
    apply Nat.one_le_pow _ _ (by positivity)
  rw [Int.subNatNat_of_le (by norm_num), Int.subNatNat_of_le h₂] at h₁
  norm_cast at h₁
  obtain ⟨N, h₁⟩ := h₁
  rw [h₁, Nat.mul_div_cancel_left _ (by norm_num)] at h₀
  -- We simplify the number under consideration using N.
  have h₃ : 2000 * 10 ^ n + ∑ k ∈ Finset.range n, 8 * 10 ^ (k + 2) + 21 = 47 * (400 * N + 43) := by
    calc
      _ = 2000 * 10 ^ n + 800 * N + 21 := by
        congr
        rw [<-h₀, Finset.mul_sum]
        congr
        ext k
        rw [Nat.pow_add]
        ring
      _ = 47 * (400 * N + 43) := by
        -- We use the fact that 10 ^ n - 1 = 9N.
        rw [show 10 ^ n = (10 - 1) * N + 1 by rw [<-h₁, Nat.sub_add_cancel h₂]]
        ring
  -- Now the goal is trivial.
  rw [h₃]
  apply Nat.not_prime_mul (by norm_num) (by omega)
