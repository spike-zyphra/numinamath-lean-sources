import Mathlib

open Real Set
open scoped BigOperators

/-x ∈ ℝ , Proof that the range of f(x) = sin^4 x + cos^2 x is [3/4 , 1]-/
theorem calculus_12318 (f : ℝ → ℝ) (hf : f = λ x => sin x ^ 4 + cos x ^ 2) :
    range f = {x | 3 / 4 ≤ x ∧ x ≤ 1} := by
        rw [hf]
        ext y
        simp [mem_range, mem_setOf_eq]
        constructor
        · -- Show that if y ∈ range f, then 3/4 ≤ y ≤ 1
            rintro ⟨x, hx⟩
            have h4 : sin x ^ 2 + cos x ^ 2 = 1 := by
                exact Real.sin_sq_add_cos_sq x
            have h5 : 3 / 4 ≤ y := by
                nlinarith [sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
            have h6 : y ≤ 1 := by
                nlinarith [sq_nonneg (sin x ^ 2), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
            constructor <;> linarith
        · -- Show that if 3/4 ≤ y ≤ 1, then y ∈ range f
            rintro ⟨h1, h2⟩
            use arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))
            have h3 : 0 ≤ 4 * y - 3 := by linarith
            have h5 : 0 ≤ Real.sqrt (4 * y - 3) := Real.sqrt_nonneg (4 * y - 3)
            have h6 : Real.sqrt (4 * y - 3) ≤ 1 := by
                have h8 : Real.sqrt (4 * y - 3) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
                rw [show Real.sqrt 1 = 1 by norm_num] at h8
                linarith
            have h7 : 0 ≤ (1 - Real.sqrt (4 * y - 3)) / 2 := by
                nlinarith [h5, h6]
            have h8 : sin (arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))) = Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) := by
                apply Real.sin_arcsin
                · -- Show that -1 ≤ Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2)
                    have h9 : 0 ≤ Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) := Real.sqrt_nonneg ((1 - Real.sqrt (4 * y - 3)) / 2)
                    linarith
                ·
                    have h10 : Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) ≤ 1 := by
                        have h12 : Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
                        rw [show Real.sqrt 1 = 1 by norm_num] at h12
                        linarith
                    linarith [h10]
            have h9 : cos (arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))) = Real.sqrt (1 - (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))^2) := by
                rw [Real.cos_arcsin]
            have h10 : (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))^2 = (1 - Real.sqrt (4 * y - 3)) / 2 := by
                exact Real.sq_sqrt (by linarith [h7])
            have h11 : sin (arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))) ^ 4 + cos (arcsin (Real.sqrt ((1 - Real.sqrt (4 * y - 3)) / 2))) ^ 2 = y := by
                rw [h8, h9, h10]
                have h12 : (Real.sqrt (1 - ((1 - Real.sqrt (4 * y - 3)) / 2)))^2 = 1 - ((1 - Real.sqrt (4 * y - 3)) / 2) := by
                    exact Real.sq_sqrt (by nlinarith [h3, h6])
                nlinarith [h12, Real.sq_sqrt (show 0 ≤ 4 * y - 3 by linarith), Real.sq_sqrt (show 0 ≤ (1 - Real.sqrt (4 * y - 3)) / 2 by linarith [h7])]
            linarith [h11]
