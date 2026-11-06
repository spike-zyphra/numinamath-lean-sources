import Mathlib.Tactic

-- Mary is $20\%$ older than Sally, and Sally is $40\%$ younger than Danielle. The sum of their ages is $23.2$ years. How old will Mary be on her next birthday?
-- $\mathrm{(A) \ } 7\qquad \mathrm{(B) \ } 8\qquad \mathrm{(C) \ } 9\qquad \mathrm{(D) \ } 10\qquad \mathrm{(E) \ }  11$

theorem alg_1167
  (m s d : ℚ)
  (s_age_relation : s = 0.6 * d)
  (m_age_relation : m = 1.2 * s)
  (sum_age : m + s + d = 23.2) :
     Rat.ceil m = 8 := by
      -- write m in terms of d(Danielle's age) since we have m in terms of s and s in terms of d
      have m_age_relation_d : m = 0.72 * d := by
        calc m = 1.2 * s := by exact m_age_relation
        _ = 1.2 * (0.6 * d) := by exact congrArg (HMul.hMul 1.2) s_age_relation
        _ = 1.2 * 0.6 * d := by exact Eq.symm (Rat.mul_assoc 1.2 0.6 d)
        _ = 0.72 * d := by ring
      -- express the sum in terms of d
      have sum_relation_d : m + s + d = 2.32 * d := by
        calc m + s + d = 0.72 * d + 0.6 * d + d := by rw [m_age_relation_d, s_age_relation]
        _ = (0.72 + 0.6 + 1) * d := by ring
        _ = 2.32 * d := by ring
      -- find d from the two equations of m + s + d
      have : 2.32 * d = 23.2 := by
        rw [sum_age] at sum_relation_d
        exact id (Eq.symm sum_relation_d)
      have h_div : d = 23.2 / 2.32 := by
        refine CancelDenoms.cancel_factors_eq_div this ?h2
        norm_num
      norm_num at h_div
      -- find m now, using d
      rw [h_div] at m_age_relation_d
      norm_num at m_age_relation_d
      rw [m_age_relation_d]
      -- we have m, just need the ceiling
      native_decide