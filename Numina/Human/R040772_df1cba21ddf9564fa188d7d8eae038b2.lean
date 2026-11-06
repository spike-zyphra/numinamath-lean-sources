import Mathlib

/- Exercise 3. Let $a, b, c \geqslant 1$ be integers such that $a^{b} \mid b^{c}$ and $a^{c} \mid c^{b}$. Show that $a^{2} \mid b c$. -/
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
  -- 2 * v_p(a) ≤ v_p(b) + v_p(c) is equivalent to
  -- b * c * (2 * v_p(a))^2 ≤ b * c * (v_p(b) + v_p(c))^2 (since b * c > 0)
  rw [←sq_le_sq₀ (by positivity) (by positivity)]
  rw [←mul_le_mul_left (show 0 < b * c by positivity)]
  -- let x = v_p(a), y = v_p(b), and z = v_p(z)
  set x := a.factorization p
  set y := b.factorization p
  set z := c.factorization p
  -- We have
  -- b * c * (2 * x) ^ 2 = 4 * (b * x) * (c * x)
  --                     ≤ 4 * (c * y) * (b * z) (from h1 and h2)
  --                     = (b * c) * (4 * y * z)
  --                     ≤ (b * c) * (y + z) ^ 2 (since 4 * y * z ≤ (y + z)^2 for any y and z)
  calc
    b * c * (2 * x) ^ 2 = 4 * (b * x) * (c * x) := by ring
    _ ≤ 4 * (c * y) * (b * z) := by gcongr
    _ = (b * c) * (4 * y * z) := by ring
    _ ≤ b * c * (y + z) ^ 2 := by gcongr; exact four_mul_le_pow_two_add y z