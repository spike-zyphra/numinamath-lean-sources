import Mathlib


theorem algebra_228614 : ∑' x : ℕ, ∑' y : ℕ, (if (5 * x + 17 * y = 307) then (x + y) else 0) = 164 := by

  have h6 : ∀ x y : ℕ, 5 * x + 17 * y = 307 → x ≤ 61 := by
    omega

  have h7 : ∀ x y : ℕ, 5 * x + 17 * y = 307 → y ≤ 18 := by
    omega

  have h8 : ∑' x : ℕ, ∑' y : ℕ, (if (5 * x + 17 * y = 307) then (x + y) else 0) =
          ∑ x in Finset.Iic 61, ∑ y in Finset.Iic 18, (if (5 * x + 17 * y = 307) then (x + y) else 0) := by

    have h9 : ∀ x : ℕ, (∑' y : ℕ, (if (5 * x + 17 * y = 307) then (x + y) else 0)) = 
      ∑ y in Finset.Iic 18, (if (5 * x + 17 * y = 307) then (x + y) else 0) := by
      intro x
      have h11 : ∀ y : ℕ, (5 * x + 17 * y = 307) → y ≤ 18 := by
        intro y h_eq
        omega

      have h13 : (∑' y : ℕ, (if (5 * x + 17 * y = 307) then (x + y) else 0)) = ∑ y in Finset.Iic 18, (if (5 * x + 17 * y = 307) then (x + y) else 0) := by
        have h14 : ∀ y : ℕ, y > 18 → (if (5 * x + 17 * y = 307) then (x + y) else 0) = 0 := by 
          intro y hy
          simp at *
          omega

        rw [tsum_eq_sum]
        intro y hy
        simp at *
        omega

      exact h13

    rw [tsum_congr h9]

    have h15 : ∀ x : ℕ, x > 61 → ∑ y in Finset.Iic 18, (if (5 * x + 17 * y = 307) then (x + y) else 0) = 0 := by
      intro x hx
      simp at *
      all_goals
      try { omega }

    rw [tsum_eq_sum]
    intro x hx
    simp at *
    all_goals
    try { omega }

  rw [h8]
  native_decide