import Mathlib

theorem algebra_19299 {a b : ℝ} (ha : a ≠ 1) (hb : b ≠ 1)
    (hroots : a ≠ b ∧ 2*a^2-7*a+2=0 ∧ 2*b^2-7*b+2=0) :
    1/(a-1)+1/(b-1)=-1 := by
  rcases hroots with ⟨hneq, ha2, hb2⟩
  have h1 : 2 * (a ^ 2 - b ^ 2) - 7 * (a - b) = 0 := by 
    linarith [ha2, hb2]
  have h2 : (a - b) * (2 * (a + b) - 7) = 0 := by
    ring_nf at h1 ⊢
    linarith
  have h3 : 2 * (a + b) - 7 = 0 := by
    apply_fun (fun x => x / (a - b)) at h2
    field_simp [sub_ne_zero.mpr hneq] at h2
    linarith
  have hab : a + b = 7 / 2 := by
    linarith
  have h4 : a * b = 1 := by
    have h7 : 2 * (a^2 + b^2) - 7 * (a + b) + 4 = 0 := by 
      nlinarith [ha2, hb2]
    have h8 : a + b = 7 / 2 := hab
    have h10 : a^2 + b^2 = (7 / 2)^2 - 2 * (a * b) := by
      have h : a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by
        ring
      rw [h, h8]
      all_goals linarith
    rw [h10] at h7
    nlinarith
  have h11 : a - 1 ≠ 0 := by
    intro h
    apply ha
    linarith
  have h12 : b - 1 ≠ 0 := by
    intro h
    apply hb
    linarith
  field_simp [h11, h12]
  nlinarith [hab, h4]