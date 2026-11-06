import Mathlib

open Real Set

/- Example 2 In $\triangle A B C$, prove: $\sin A+\sin B+\sin C \leqslant \frac{3 \sqrt{3}}{2}$. -/

--We use the fact that the sine function is concave on the interval [0, π] to prove that sin ((A + B + C) / 3) ≥ (sin A + sin B + sin C) / 3.
lemma conc (A B C : Real) (hA : A ∈ Ioo 0 π) (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) : sin ((A + B + C) / 3) ≥ (sin A + sin B + sin C) / 3 := by
--We use the fact, proven in Mathlib, that the sine function is strictly concave on the interval [0, π].
  have conc := strictConcaveOn_sin_Icc
--We deduce that sine is concave on the interval [0, π] and apply the definition of concavity.
  apply StrictConcaveOn.concaveOn at conc
  rw [concaveOn_iff_forall_pos] at conc
  obtain ⟨convset,concave⟩ := conc
--We use the definition of concavity to show that 1/3 sin A + 2/3 sin ((B + C) / 2) ≤ sin (1/3 A + 2/3 ((B + C) / 2))
  have hA' : A ∈ Icc 0 π := by
    simp only [mem_Icc]
    simp only [mem_Ioo] at hA
    obtain ⟨hA1, hA2⟩ := hA
    exact ⟨by linarith, by linarith⟩
  have concave2 := concave
  have hBC : (B + C) / 2 ∈ Icc 0 π := by
    simp only [mem_Icc]
    simp only [mem_Ioo] at hB hC
    obtain ⟨hB1, hB2⟩ := hB
    obtain ⟨hC1, hC2⟩ := hC
    exact ⟨by linarith, by linarith⟩
  set a := (1 : ℝ) / 3 with ha
  set b := (2 : ℝ) / 3 with hb
  have hapos : 0 < a := by norm_num
  have hbpos : 0 < b := by norm_num
  have hab : a + b = 1 := by norm_num
  specialize concave hA' hBC hapos hbpos hab
  rw [ha, hb, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at concave
  ring_nf at concave
--We use again the definition of concavity to show that 1/2 sin B + 1/2 sin C ≤ sin ((B + C)/2).
  have hB' : B ∈ Icc 0 π := by
    simp only [mem_Icc]
    simp only [mem_Ioo] at hB
    obtain ⟨hB1, hB2⟩ := hB
    exact ⟨by linarith, by linarith⟩
  have hC' : C ∈ Icc 0 π := by
    simp only [mem_Icc]
    simp only [mem_Ioo] at hC
    obtain ⟨hC1, hC2⟩ := hC
    exact ⟨by linarith, by linarith⟩
  set a2 := (1 : ℝ) / 2 with ha2
  set b2 := (1 : ℝ) / 2 with hb2
  rw [ha2, hb2] at concave
  have hapos2 : 0 < a2 := by norm_num
  have hbpos2 : 0 < b2 := by norm_num
  have hab2 : a2 + b2 = 1 := by norm_num
  specialize concave2 hB' hC' hapos2 hbpos2 hab2
  rw [ha2, hb2, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at concave2
--Combining the two inequalities together we obtain the claim.
  have : sin A * (1 / 3) + sin (B * (1 / 2) + C * (1 / 2)) * (2 / 3) ≥ sin A * (1 / 3) + (1 / 2 * sin B + 1 / 2 * sin C) * (2 / 3) := by
    gcongr
    rw [mul_comm B, mul_comm C]
    exact concave2
  ring_nf at this
  ring_nf
  apply le_trans this
  rw [add_comm _ (A * (1 / 3)), ← add_assoc] at concave
  exact concave






--We are now ready to prove the theorem.
theorem inequalities_261080 (A B C : Real) (hA : A ∈ Ioo 0 π) (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) : sin A + sin B + sin C ≤ 3 * sqrt 3 / 2 := by
--We will use the result from the lemma "conc" to prove the theorem.
  have conc := conc A B C hA hB hC
--Since A + B + C = π, we can rewrite the left-hand side of the inequality as sin (π / 3), which is equal to √3/2.
  rw [hABC] at conc
  have : sin (π / 3) = sqrt 3 / 2 := by
    rw [sin_pi_div_three]
  rw [this] at conc
--The inequality obtained is equivalent to the claim.
  linarith