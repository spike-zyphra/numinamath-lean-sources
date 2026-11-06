import Mathlib
open Polynomial

/- Let $p(x)$ be a monic polynomial of degree 4, such that $p(1) = 17,$ $p(2) = 34,$ and $p(3) = 51.$  Find $p(0) + p(4).$ -/
theorem algebra_13755 {p : Polynomial ℝ} (hp : p.Monic) (h0 : p.natDegree = 4) (h1 : p.eval 1 = 17) (h2 : p.eval 2 = 34) (h3 : p.eval 3 = 51) :
    p.eval 0 + p.eval 4 = 92 := by
  -- Take the factor (X - 1) out of P(X) - 17X.
  replace h1 : X - C 1 ∣ p - C 17 * X := by
    rw [dvd_iff_isRoot]
    simp [h1]
  rw [dvd_def] at h1
  obtain ⟨p₁, h1⟩ := h1
  -- Take the factor (X - 2) out.
  replace h2 : X - C 2 ∣ p - C 17 * X := by
    rw [dvd_iff_isRoot]
    simp [h2]
    norm_num
  rw [h1] at h2
  apply Prime.left_dvd_or_dvd_right_of_dvd_mul at h2
  pick_goal 2
  apply prime_X_sub_C
  obtain h2 | h2 := h2
  rw [dvd_iff_isRoot] at h2
  simp at h2
  absurd h2
  norm_num
  rw [dvd_def] at h2
  obtain ⟨p₂, h2⟩ := h2
  -- Take the factor (X - 3) out.
  replace h3 : X - C 3 ∣ p - C 17 * X := by
    rw [dvd_iff_isRoot]
    simp [h3]
    norm_num
  rw [h1] at h3
  apply Prime.left_dvd_or_dvd_right_of_dvd_mul at h3
  pick_goal 2
  apply prime_X_sub_C
  obtain h3 | h3 := h3
  rw [dvd_iff_isRoot] at h3
  simp at h3
  absurd h3
  norm_num
  rw [h2] at h3
  apply Prime.left_dvd_or_dvd_right_of_dvd_mul at h3
  pick_goal 2
  apply prime_X_sub_C
  obtain h3 | h3 := h3
  rw [dvd_iff_isRoot] at h3
  simp at h3
  absurd h3
  norm_num
  rw [dvd_def] at h3
  obtain ⟨p₃, h3⟩ := h3
  rw [h2, h3] at h1
  clear h2 h3
  -- Getting some lemmas.
  have g1 : ((X - C 1) * ((X - C 2) * ((X - C 3) * p₃))).leadingCoeff ≠ 0 := by
    rw [<-h1]
    by_contra!
    simp at this
    have weq : 0 = 4 := by
      calc
        0 = (0 : Polynomial ℝ).natDegree := by rw [Polynomial.natDegree_zero]
        _ = (p - C 17 * X).natDegree := by rw [this]
        _ = p.natDegree := by rw [natDegree_sub_eq_left_of_natDegree_lt]; rw [Polynomial.natDegree_C_mul_X, h0]; norm_num; norm_num
        _ = 4 := by exact h0
    linarith only [weq]
  have g2 : ((X - C 2) * ((X - C 3) * p₃)).leadingCoeff ≠ 0 := by
    have g2 := g1
    rw [leadingCoeff_mul, mul_ne_zero_iff] at g2
    tauto
  have g3 : ((X - C 3) * p₃).leadingCoeff ≠ 0 := by
    have g3 := g2
    rw [leadingCoeff_mul, mul_ne_zero_iff] at g3
    tauto
  -- Prove that p₃ has degree one.
  have h4 : 1 + (1 + (1 + p₃.natDegree)) = 4 := by
    calc
      1 + (1 + (1 + p₃.natDegree)) = 1 + (1 + (((X - C 3) * p₃).natDegree)) := by rw [natDegree_mul', natDegree_X_sub_C]; rw [<-Polynomial.leadingCoeff_mul]; exact g3
      _ = 1 + ((X - C 2) * ((X - C 3) * p₃)).natDegree := by nth_rewrite 2 [natDegree_mul']; rw [natDegree_X_sub_C]; rw [<-Polynomial.leadingCoeff_mul]; exact g2
      _ = ((X - C 1) * ((X - C 2) * ((X - C 3) * p₃))).natDegree := by nth_rewrite 2 [natDegree_mul']; rw [natDegree_X_sub_C]; rw [<-Polynomial.leadingCoeff_mul]; exact g1
      _ = (p - C 17 * X).natDegree := by rw [h1]
      _ = p.natDegree := by rw [natDegree_sub_eq_left_of_natDegree_lt]; rw [Polynomial.natDegree_C_mul_X, h0]; norm_num; norm_num
      _ = 4 := by exact h0
  replace h4 : p₃.natDegree = 1 := by
    linarith only [h4]
  -- Prove that p₃ is monic.
  have k1 : ((X - C 1) * ((X - C 2) * ((X - C 3) * p₃))).Monic := by
    rw [<-h1]
    apply Polynomial.Monic.sub_of_left hp
    rw [degree_eq_natDegree, degree_eq_natDegree]
    simp [h0]
    by_contra!
    have weq : 0 = 4 := by
      calc
        0 = (0 : Polynomial ℝ).natDegree := by rw [Polynomial.natDegree_zero]
        _ = p.natDegree := by rw [this]
        _ = 4 := by exact h0
    linarith only [weq]
    simp
  have k2 : ((X - C 2) * ((X - C 3) * p₃)).Monic := by
    apply Polynomial.Monic.of_mul_monic_left (show (X - C 1 : Polynomial ℝ).Monic by apply monic_X_sub_C)
    exact k1
  have k3 : ((X - C 3) * p₃).Monic := by
    apply Polynomial.Monic.of_mul_monic_left (show (X - C 2 : Polynomial ℝ).Monic by apply monic_X_sub_C)
    exact k2
  have k4 : p₃.Monic := by
    apply Polynomial.Monic.of_mul_monic_left (show (X - C 3 : Polynomial ℝ).Monic by apply monic_X_sub_C)
    exact k3
  -- Now p₃ is of the form of X + r.
  apply Monic.eq_X_add_C k4 at h4
  rw [h4] at h1
  have eq1 : eval 4 (p - C 17 * X) = eval 4 ((X - C 1) * ((X - C 2) * ((X - C 3) * (X + C (p₃.coeff 0))))) := by
    rw [h1]
  norm_num [<-mul_assoc] at eq1
  have eq2 : eval 0 (p - C 17 * X) = eval 0 ((X - C 1) * ((X - C 2) * ((X - C 3) * (X + C (p₃.coeff 0))))) := by
    rw [h1]
  norm_num [<-mul_assoc] at eq2
  -- Finally calculate eval 0 p + eval 4 p.
  calc
    eval 0 p + eval 4 p = (eval 4 p - 68) + 68 + eval 0 p := by ring_nf
    _ = 6 * (4 + p₃.coeff 0) + 68 + -(6 * p₃.coeff 0) := by rw [eq1, eq2]
    _ = 92 := by ring_nf
