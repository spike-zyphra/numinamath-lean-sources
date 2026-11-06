import Mathlib

theorem number_theory_293960
    (a b c : ℕ)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hc : 1 ≤ c)
    (h1 : a^b ∣ b^c)
    (h2 : a^c ∣ c^b) :
    a^2 ∣ b * c := by
-- It is enough to show that the multiplicity (Nat.factorization) of p in a^2 is less of equal
  -- than the multiplicity of p in b * c for all p.
  -- Write v_p(k) for the multiplicity of p in k.
  rw [←Nat.factorization_le_iff_dvd (by nlinarith) (by nlinarith)]
  intro p
  -- Simplify the goal and hypotheses h1, h2.
  -- We have to prove that
  -- 2 * v_p(a) ≤ v_p(b) + v_p(c)
  -- given that
  -- h1: b * v_p(a) ≤ c * v_p(b)
  -- h2: c * v_p(a) ≤ b * v_p(c)
  rw [Nat.factorization_pow, Nat.factorization_mul (by linarith) (by linarith)]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.coe_add, Pi.add_apply]
  rw [←Nat.factorization_le_iff_dvd (ne_of_gt (by positivity)) (ne_of_gt (by positivity))] at h1
  rw [←Nat.factorization_le_iff_dvd (ne_of_gt (by positivity)) (ne_of_gt (by positivity))] at h2
  specialize h1 p
  specialize h2 p
  simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h1 h2
  have h3 : (2 : ℝ) * (a.factorization p) ≤ (b.factorization p + c.factorization p) := by
    have h1' : (b : ℝ) * (a.factorization p : ℝ) ≤ (c : ℝ) * (b.factorization p : ℝ) := by
      exact_mod_cast h1
    have h2' : (c : ℝ) * (a.factorization p : ℝ) ≤ (b : ℝ) * (c.factorization p : ℝ) := by
      exact_mod_cast h2
    nlinarith [sq_nonneg ((a.factorization p) : ℝ), 
          sq_nonneg ((b.factorization p - c.factorization p) : ℝ), 
          sq_nonneg ((b : ℝ) - (c : ℝ)), 
          mul_pos (show (0 : ℝ) < (b : ℝ) by exact_mod_cast (show 0 < (b : ℕ) by linarith) ) 
          (show (0 : ℝ) < (c : ℝ) by exact_mod_cast (show 0 < (c : ℕ) by linarith) )
         ]
  exact_mod_cast h3