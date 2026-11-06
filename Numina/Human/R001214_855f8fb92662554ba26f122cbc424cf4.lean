import Mathlib

theorem algebra_21391 (P : Cubic ℝ) (hP : P = ⟨1, -20, 18, -7⟩) (r s t : ℝ) (h : P.roots = {r, s, t}) : r^2*s^2+s^2*t^2+t^2*r^2=44 := by
  have h₁ : P.a ≠ 0 := by simp [hP]
  have h₂ : P = Cubic.map (RingHom.id ℝ) P := by rw [Cubic.map]; simp
  rw [h₂] at h
  have hb := Cubic.b_eq_three_roots h₁ h
  have hc := Cubic.c_eq_three_roots h₁ h
  have hd := Cubic.d_eq_three_roots h₁ h
  -- Vieta theorem
  simp [hP] at hb hc hd
  have hb₁ : 20 = r + s + t := by rw [← neg_neg 20, hb]; ring
  have : (r*s+r*t+s*t)^2=r^2*s^2+s^2*t^2+t^2*r^2+2*(r*s*t)*(r+s+t) := by norm_cast; ring
  rw [← hb₁, ← hc, ← hd] at this
  symm at this
  have := eq_sub_of_add_eq this
  norm_num at this
  norm_cast