import Mathlib

open Real
open scoped BigOperators

theorem algebra_168757 {A : ℕ → ℝ} (hA : ∀ k, A k = (19^k + 66^k) / Nat.factorial k) :
    IsGreatest (Set.image A (Finset.Icc 1 65)) (A 65) := by

  constructor
  · -- Show that A 65 is in the image of A over [1, 65].
    rw [Set.mem_image]
    use 65
    simp [Finset.mem_Icc, hA]
    all_goals norm_num

  · -- Show that A 65 is the greatest in the image.
    intro y hy
    rw [Set.mem_image] at hy
    rcases hy with ⟨k, hk⟩
    simp [Finset.mem_Icc] at hk
    have h_eq : A k = (19 ^ k + 66 ^ k) / Nat.factorial k := hA k
    have h_eq2 : A 65 = (19 ^ 65 + 66 ^ 65) / Nat.factorial 65 := hA 65

    have h3 : A k ≤ A 65 := by
      rw [h_eq, h_eq2]

      have h4 : (19 ^ k + 66 ^ k : ℝ) / Nat.factorial k ≤ (19 ^ 65 + 66 ^ 65 : ℝ) / Nat.factorial 65 := by
        have h5 : (Nat.factorial k : ℝ) > 0 := by positivity
        have h6 : (Nat.factorial 65 : ℝ) > 0 := by positivity
        have h7 : (19 ^ k + 66 ^ k : ℝ) * (Nat.factorial 65) ≤ (19 ^ 65 + 66 ^ 65 : ℝ) * (Nat.factorial k) := by
          have h8 : k ≤ 65 := by linarith
          interval_cases k <;> norm_num [Nat.factorial] at *
          <;> norm_num

        have h8 : (19 ^ k + 66 ^ k : ℝ) / Nat.factorial k ≤ (19 ^ 65 + 66 ^ 65 : ℝ) / Nat.factorial 65 := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          linarith [h7]
        linarith

      linarith

    linarith [show A k ≤ A 65 from h3, hk]