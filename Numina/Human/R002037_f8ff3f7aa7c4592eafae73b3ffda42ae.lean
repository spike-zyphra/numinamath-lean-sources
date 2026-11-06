import Mathlib

open Real

/- The number of solutions, in real numbers $a$, $b$, and $c$, to the system of equations $$a+bc=1,$$$$b+ac=1,$$$$c+ab=1,$$ is

$\text{(A) }3\qquad\text{(B) }4\qquad\text{(C) }5\qquad\text{(D) more than }5\text{, but finitely many}\qquad\text{(E) infinitely many}$ -/
theorem algebra_58320 :
  {(a, b, c) : ℝ × ℝ × ℝ | a + b * c = 1 ∧ b + a * c = 1 ∧ c + a * b = 1}.ncard = 5 := by

  let phi1 := (-1 - sqrt 5) / 2
  let phi2 := (-1 + sqrt 5) / 2

  have h_phi1 : phi1 + phi1 * phi1 = 1 := by
    unfold phi1
    ring_nf
    rw [sq_sqrt (by positivity)]
    linarith

  have h_phi2 : phi2 + phi2 * phi2 = 1 := by
    unfold phi2
    ring_nf
    rw [sq_sqrt (by positivity)]
    linarith

  have h_solve :  {(a, b, c) : ℝ × ℝ × ℝ | a + b * c = 1 ∧ b + a * c = 1 ∧ c + a * b = 1} = {(0,1,1),(1,0,1),(1,1,0),(phi1,phi1,phi1),(phi2,phi2,phi2)} := by
    ext ⟨a,b,c⟩
    simp only [Set.mem_setOf_eq]

    constructor
    . intro ⟨hx1, hx2, hx3⟩
      have : c = 1 - a * b := by linarith
      subst c

      by_cases ha1 : a = -1
      . subst a
        ring_nf at hx2
        norm_num at hx2

      . have : a + 1 ≠ 0 := by
          by_contra
          have : a = -1 := by linarith
          tauto

        by_cases ha0 : a = 1
        . subst a
          -- ring_nf at *
          have : b * (b - 1) = 0 := by linarith
          simp at this
          rcases this with rfl | h
          . right; left
            simp
          . right; right; left
            have : b = 1 := by linarith
            subst b
            simp

        . have : b = 1 / (a+1) := by
            field_simp

            have : (1-a)*((1+a)*b-1)=0:= by linarith
            simp at this
            rcases this with h1 | h2
            . have : a = 1 := by linarith
              tauto
            . linarith

          subst b
          field_simp at hx1
          ring_nf at hx1

          have : a ^ 3 = a - a ^ 2 := by linarith

          have : a * (a^2+a-1)=0 := by
            ring_nf
            rw [this]
            ring_nf

          simp at this

          rcases this with rfl | h
          . left
            simp
          . right;right;right
            have : 1 / (a + 1) = a := by
              field_simp
              linarith

            rw [this]

            have : 1 - a * a = a := by linarith
            rw [this]

            have : (a-phi1)*(a-phi2)=0 := by
              ring_nf
              rw [sq_sqrt (by positivity)]
              linarith

            simp at this
            rcases this with h1 | h2
            . have : a = phi1 := by linarith
              subst a
              simp
            . have : a = phi2 := by linarith
              subst a
              simp

    . intro hx
      rcases hx with h | h | h | h | h
      all_goals simp at h; rw [h.1, h.2.1, h.2.2]; simp
      all_goals assumption

  rw [h_solve]

  have : √5 ≥ 0 := by positivity
  have h0 : phi1 ≠ phi2 := by
    by_contra h
    unfold phi1 at h
    unfold phi2 at h
    have : √5 = 0 := by linarith
    rw [sqrt_eq_iff_eq_sq (by positivity) (by positivity)] at this
    linarith

  have h1 : (1 = phi1) = False := by
    simp
    by_contra h
    unfold phi1 at h
    linarith

  have h2 : (1 = phi2) = False := by
    simp
    by_contra h
    unfold phi2 at h
    have : √5 = 3 := by linarith
    rw [sqrt_eq_iff_eq_sq (by positivity) (by positivity)] at this
    linarith

  have h3 : (0 = phi1) = False := by
    simp
    by_contra h
    unfold phi1 at h
    linarith

  have h4 : (0 = phi2) = False := by
    simp
    by_contra h
    unfold phi2 at h
    have : √5 = 1 := by linarith
    rw [sqrt_eq_iff_eq_sq (by positivity) (by positivity)] at this
    linarith

  repeat rw [Set.ncard_insert_of_not_mem]

  all_goals simp
  . assumption
  . rw [h1, h2]
    simp
  . rw [h1, h2]
    simp
  . rw [h3, h4]
    simp
