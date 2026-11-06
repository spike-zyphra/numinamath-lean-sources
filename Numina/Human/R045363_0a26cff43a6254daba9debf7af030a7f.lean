import Mathlib

/- Three integers form a geometric progression. If we add 8 to the second number, an arithmetic progression is formed. If we add 64 to the third term of this arithmetic progression, we again get a geometric progression. What are the original numbers? -/
theorem algebra_229830 {a b c : ℤ} (h₀ : b^2 = a * c) (h₁ : 2*(b+8) = a+c) (h₂ : (b + 8)^2 = a * (c+64)) :
    a = 4 ∧ b = 12 ∧ c = 36 := by
    -- we need to check if a is 0(Hint: it's not)
    by_cases ha : a = 0
    · have h₀' := h₀; rw [ha] at h₀'; simp at h₀'; rw [ha, h₀'] at h₂; linarith
    -- since a b c are in geometric progression, we can write b = a*q, c=a*q^2
    let q':∃ q:ℝ, b = a*q ∧ c = a*q^2 := by
      use b/a; ring_nf; constructor
      · rw [mul_comm (a:ℝ), mul_assoc, mul_inv_cancel₀ (by simp; exact ha)]; simp
      · norm_cast
        rw [h₀]; ring_nf
        apply Eq.symm
        calc _
        _ = ↑(a ^ 2) * ↑c * (a:ℝ)⁻¹ ^ 2 := by rw [Int.cast_mul];
        _ = (a:ℝ) * (a:ℝ) * (c:ℝ) * (a:ℝ)⁻¹ * (a:ℝ)⁻¹ := by rw [Int.cast_pow]; ring_nf
        _ = ((a:ℝ) * (a:ℝ)⁻¹) * ((a:ℝ) * (a:ℝ)⁻¹) * (c:ℝ) := by ring_nf
        _ = (c:ℝ) := by rw [mul_inv_cancel₀ (by simp; exact ha), one_mul, one_mul]
    obtain ⟨q, ⟨qdefb, qdefc⟩⟩ := q'
    -- rewrite assumptions in terms of q (and a)
    rify at h₁ h₂
    rw [qdefb, qdefc] at h₁ h₂
    -- rewrite equations to get rid of a
    apply congr_arg (fun x => -x + a + a*q^2 + 16) at h₁
    ring_nf at h₁
    conv_lhs at h₁ =>
      calc _
      _ = a* (1- 2*q + q ^ 2)  := by ring_nf
    apply congr_arg (fun x => (x - a * 64 - a ^ 2 * q ^ 2)/16 - 4) at h₂
    ring_nf at h₂
    conv_lhs at h₂ =>
      calc _
      _ = a * (q-4) := by ring_nf
    -- we can divide the equations to get rid of a
    have h3: a * (1-2*q+q^2) / (a * (q-4)) = 16/(-4) := by
      norm_num
      rw [h₁ , h₂]; norm_num
    conv_lhs at h3=>
      calc _
      _ = ↑a * (1 - 2 * q + q ^ 2) * (1/ (↑a * (q - 4))) := by ring_nf
      _ = a * (1 - 2 * q + q ^ 2) * (1/a * 1 /(q - 4)) := by apply congr_arg (fun x=> a * (1 - 2 * q + q ^ 2) * x); field_simp
      _ = (a/a) * (1 - 2 * q + q ^ 2) * (1 /(q - 4)) := by ring_nf
      _ = (1 - 2 * q + q ^ 2) / (q-4) := by rw [div_self (by simp; assumption)]; ring_nf
    norm_num at h3
    -- to be able to deal with q-4 we need to show that q-4 is not 0
    by_cases hq4 : q - 4 = 0
    · have q4: q=4 := by linarith
      rw [q4] at h₁; norm_num at h₁
      -- this is a clear contradiction since a is an integer
      norm_cast at h₁
      apply Dvd.intro_left at h₁
      norm_num at h₁
    apply congr_arg (fun x => x * (q - 4)) at h3
    conv_lhs at h3 =>
      calc _
      _ = (1 - 2 * q + q ^ 2) * ((q-4)/(q-4)) := by ring_nf
      _ = 1 - 2 * q + q ^ 2 := by rw [div_self (by simp; assumption), mul_one];
    apply congr_arg (fun x => x + 4 *(q-4)) at h3; ring_nf at h3
    -- now we have a simple quadratic equation
    have sol := (quadratic_eq_zero_iff (a:=(1:ℝ)) (b:=(2:ℝ)) (c:=(-15:ℝ)) (by norm_num) (s:=8) (by unfold discrim; norm_num) q).mp
    ring_nf at sol
    specialize sol h3
    -- we get two solutions, negative is invalid
    cases' sol with sol' sol'
    · rw [sol'] at h₁; norm_num at h₁; have ha:(a:ℝ) =4 := by linarith
      norm_cast at ha
      exact ⟨ha, ⟨by rify; rw [qdefb, ha, sol']; norm_num, by rify; rw [qdefc, ha, sol']; norm_num⟩⟩
    · rw [sol'] at h₁; norm_num at h₁;
      -- again a contradiciton with a being an integer
      norm_cast at h₁
      apply Dvd.intro_left at h₁
      norm_num at h₁