import Mathlib

/- How many multiples of 7 between $10^{6}$ and $10^{9}$ are perfect squares?-/
theorem number_theory_610944 :
    Set.encard {n : ℕ | 7 ∣ n ∧ IsSquare n ∧ 10 ^ 6 ≤ n ∧ n ≤ 10 ^ 9} = 4375 := by
  -- We modify the content of the set to make it easier to work with.
  calc
    Set.encard {n : ℕ | 7 ∣ n ∧ IsSquare n ∧ 10 ^ 6 ≤ n ∧ n ≤ 10 ^ 9}
    _ = Set.encard {n : ℕ | ∃ k, 142 < k ∧ k < 4518 ∧ n = (7 * k) ^ 2} := by
      -- Prove that such values of n are exactly multiples of 49 in the range, so the two sets are equal.
      congrm Set.encard ?_
      -- Break the goal into two parts.
      ext n
      apply Iff.intro
      . -- Show that if n is in the set on the left, then n is in the set on the right.
        simp
        intro h₀ h₁ h₂ h₃
        -- We have 7 ∣ n, so n = 7 * m for some m.
        obtain ⟨m, h₁⟩ := h₁
        -- We have 7 ∣ m.
        rw [h₁, <-pow_two] at h₀
        apply Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 7 by decide) at h₀
        rw [dvd_iff_exists_eq_mul_right] at h₀
        obtain ⟨k, h₀⟩ := h₀
        use k
        exact ⟨by nlinarith, by nlinarith, by rw [h₁, h₀, pow_two]⟩
      . -- Show that if n is in the set on the right, then n is in the set on the left.
        simp
        intro k h₀ h₁ h₂
        refine ⟨?_, ?_, ?_, ?_⟩
        . -- We have 7 ∣ n.
          rw [h₂, pow_two, mul_assoc]
          apply Nat.dvd_mul_right
        . -- n is a square.
          use 7 * k
          linarith only [h₂]
        . -- 10⁶ ≤ n.
          nlinarith
        . -- n ≤ 10⁹.
          nlinarith
    _ = Set.encard {k : ℕ | 142 < k ∧ k < 4518} := by
      -- Since we are considering the number of elements, we change to counting k instead of counting n.
      -- Create a bijection between the two sets.
      let φ : {k : ℕ | 142 < k ∧ k < 4518} → {n : ℕ | ∃ k, 142 < k ∧ k < 4518 ∧ n = (7 * k) ^ 2} := fun k ↦ ⟨(7 * k) ^ 2, ?_⟩
      pick_goal 2
      -- Show that (7k)² belongs to the set on the right if k belongs to the set on the left, so that φ is a function.
      obtain ⟨k, h₀, h₁⟩ := k
      simp
      tauto
      -- With bijection φ, the two sets have the same cardinality.
      refine (Set.encard_congr (Equiv.ofBijective φ ⟨fun a b heq ↦ ?_, fun ⟨n, k, h₀, h₁, h₂⟩ ↦ ?_⟩)).symm
      . -- Show that φ is injective.
        obtain ⟨a, h₀, h₁⟩ := a
        obtain ⟨b, h₂, h₃⟩ := b
        simp [φ] at heq
        congr
      . -- Show that φ is surjective.
        simp [φ]
        use k
        tauto
    _ = Set.encard ((Finset.Ioo 142 (4518 : ℕ)).toSet) := by
      -- We get k in the range (142, 4518).
      congrm Set.encard ?_
      simp [Set.Ioo]
    _ = 4375 := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      simp
