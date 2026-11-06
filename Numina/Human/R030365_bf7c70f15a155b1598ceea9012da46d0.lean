import Mathlib

open Real

theorem algebra_325801 {f : ℝ → ℝ} (hf : ∀ x, f x =
    (sqrt 2 * sin (x + π / 4) + 2 * x ^ 2 + x) / (2 * x ^ 2 + cos x))
    (hmax : IsGreatest (f '' Set.univ) M) (hmin : IsLeast (f '' Set.univ) m) :
    M + m = 2 := by
  replace hf : ∀ x, f x = (sin x + x) / (2 * x ^ 2 + cos x) + 1 := by
    intro x; rw [hf, sin_add, div_add_one]; simp
    ring_nf; norm_num; ring
    by_cases h : 1 < x ^ 2
    · rw [← abs_pos]; calc
        _ < |(2 : ℝ) * 1| - |1| := by norm_num
        _ ≤ |2 * x ^ 2| - |-cos x| := by
          apply sub_le_sub; gcongr
          norm_num; exact abs_cos_le_one x
        _ ≤ _ := by rw [← sub_neg_eq_add]; apply abs_sub_abs_le_abs_sub
    intro h'; push_neg at h; rw [sq_le_one_iff_abs_le_one] at h
    suffices : 0 < cos x; linarith only [h', this, sq_nonneg x]
    exact cos_pos_of_le_one h
  simp [IsGreatest, upperBounds, hf] at hmax
  simp [IsLeast, lowerBounds, hf] at hmin
  rcases hmax with ⟨⟨t, ht⟩, hmax⟩
  rcases hmin with ⟨⟨t', ht'⟩, hmin⟩
  specialize hmax (-t'); specialize hmin (-t)
  simp at hmax hmin; rw [← neg_add, neg_div] at hmax hmin
  linarith