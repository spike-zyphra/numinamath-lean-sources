import Mathlib

open Real Set
open scoped BigOperators

/-The minimum positive period $T$ of the function $f(x)=\begin{vmatrix}\sin x+\cos x & \cos (\pi-x) \\ 2\sin x & \cos x-\sin x\end{vmatrix}$ is \_\_\_\_\_\_\_\_\_\_\_\_.-/
theorem algebra_9080 {f : ℝ → ℝ}
  (hf : f = λ x => Matrix.det !![sin x + cos x, cos (π - x); 2 * sin x, cos x - sin x]) :
  IsLeast {T | 0 < T ∧ Function.Periodic f T} (Real.pi) := by
    simp at hf
    -- Given: $f(x)=\begin{vmatrix}\sin x+\cos x & \cos (\pi-x) \\ 2\sin x & \cos x-\sin x\end{vmatrix}$
    -- $=(\sin x+\cos x)(\cos x-\sin x)-2\sin x\cos (\pi-x)$
    -- $=\sin \left(2x+ \dfrac{\pi}{4}\right)$,
    have h1 : f = fun x ↦ √2 * sin (2 * x + π / 4) := by
      simp [hf]
      ext x
      simp [sin_add, sin_two_mul, cos_two_mul]
      ring_nf
      simp [sq_sqrt]
      rw [sub_add_comm, ←Real.cos_two_mul']
      rw [show (2 : ℝ) * (-1 / 2) = -1 by linarith, ←sub_eq_add_neg]
      rw [add_sub_assoc, show cos x ^ 2 * 2 - 1 = 2 * cos x ^ 2 - 1 by linarith, ←Real.cos_two_mul]
      ring
    -- An auxiliary lemma : the minimum positive period of function
    -- $y=A * sin (a * x + b) + c$ is `2 * π / |a|`.
    have sin_periodic_Aabc {f : ℝ → ℝ} (A a b c : ℝ) (hA : A ≠ 0) (ha : a ≠ 0) (hf : f = fun x => A * sin (a * x + b) + c) :
    IsLeast {T : ℝ | 0 < T ∧ Function.Periodic f T} (2 * π / |a|) := by
      constructor
      · simp
        constructor
        · positivity
        · intro x
          simp [hf]
          ring_nf
          nth_rw 2 [add_comm]
          rw [add_assoc, sin_add]
          by_cases apos : 0 < a
          · simp [abs_of_pos apos]
            field_simp
            simp [show π * 2 = 2 * π by ring]
          · push_neg at apos
            simp [abs_of_neg (lt_of_le_of_ne apos ha)]
            ring_nf
            field_simp
            simp [show π * 2 = 2 * π by ring]
      · rintro T ⟨h1, h2⟩
        by_contra h3
        push_neg at h3
        specialize h2 ((π / 2 - b) / a)
        simp [hf, hA] at h2
        rw [mul_add, show a * ((π / 2 - b) / a) = π / 2 - b by field_simp; linarith] at h2
        norm_num at h2
        ring_nf at h2
        rw [←div_eq_mul_one_div, sin_add] at h2
        simp at h2
        obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (a * T)).1 h2
        have nne0 : n ≠ 0:= fun n0 => by simp [n0] at hn; simp [ha, h1] at hn; linarith
        have nabslt1 : |n| < 1 := by
          have : |n * (2 * π)| < 2 * π := (abs_eq_abs.2 (Or.inl hn)) ▸ (by
            calc _ = |a| * T := by rw [ abs_mul, abs_of_pos h1]
                _ < |a| *  (2 * π / |a|) := (mul_lt_mul_left (by simp [ha])).mpr h3
                _ = _ := by field_simp)
          simp [abs_mul, abs_of_pos Real.pi_pos] at this
          have : |(n:ℝ)| < 1 := by
            nth_rw 2 [←one_mul (2 * π)] at this
            exact (mul_lt_mul_right (by simp [Real.pi_pos])).1 this
          norm_cast at this
        simp at nabslt1
        exact nne0 nabslt1
    -- Using the above lemma, the minimum positive period of
    -- $f(x)=\begin{vmatrix}\sin x+\cos x & \cos (\pi-x) \\ 2\sin x & \cos x-\sin x\end{vmatrix}$ is $\pi$.
    convert sin_periodic_Aabc √2 2 (π / 4) 0 (by simp) (by simp) (by convert h1 using 1; simp)
    simp
