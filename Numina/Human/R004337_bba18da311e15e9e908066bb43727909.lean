import Mathlib

lemma f_solve {x : ℝ}
  (hx: x^3+x=2): x=1:= by

  let f1 : ℝ → ℝ := fun x => x^3
  let f2 : ℝ → ℝ := fun x => x
  let f3 : ℝ → ℝ := fun x => x^3 + x

  have hf1 : Monotone f1 := by
    intro x y hxy
    unfold f1
    nlinarith [sq_nonneg (y - x), sq_nonneg (y + x)]

  have hf2 : StrictMono f2 := by
    intro x y hxy
    unfold f2
    exact hxy

  have hf3 : StrictMono f3 := by
    exact Monotone.add_strictMono hf1 hf2

  rcases lt_trichotomy x 1 with hx | hx | hx
  . have := hf3 hx
    unfold f3 at this
    linarith
  . exact hx
  . have := hf3 hx
    unfold f3 at this
    linarith

theorem algebra_254279 (a b c d : ℝ) :
  a + b * c * d = 2 ∧ b + a * c * d = 2 ∧ c + a * b * d = 2 ∧ d + a * b * c = 2
  ↔ (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1)
  ∨ (a = -1 ∧ b = -1 ∧ c = -1 ∧ d = 3)
  ∨ (a = -1 ∧ b = -1 ∧ c = 3 ∧ d = -1)
  ∨ (a = -1 ∧ b = 3 ∧ c = -1 ∧ d = -1)
  ∨ (a = 3 ∧ b = -1 ∧ c = -1 ∧ d = -1) := by

  refine Iff.intro ?_ $ by
    intro h
    rcases h with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
    all_goals subst a b c d; ring_nf; simp

  intro ⟨ha, hb, hc, hd⟩

  have h_ab : (b - a) * (c * d - 1) = 0 := by
    linarith
  simp at h_ab

  have h_cd : (d - c) * (a * b - 1) = 0 := by
    linarith
  simp at h_cd

  rcases h_ab with h_ab1 | h_ab2
  . replace h_ab1 : a = b := by linarith

    subst a
    rcases h_cd with h_cd1 | h_cd2
    . replace h_cd1 : c = d := by linarith
      subst c

      have h_bd1 :  (b * d - 1) * (d - b) = 0 := by
        linarith

      simp at h_bd1
      rcases h_bd1 with h_bd1 | h_bd1
      . have h_bd2 : b * d = 1 := by
          linarith

        rw [h_bd2] at ha

        have h_bd2 : b = 2 - d := by
          linarith
        rw [h_bd2] at h_bd1
        have : (d-1)^2 = 0 := by
          linarith
        simp at this
        have h_bd3 : d = 1 := by
          linarith
        subst d
        simp; norm_num
        linarith

      . have h_bd2 : d = b := by
          linarith

        subst d
        norm_num at *
        have : b^3+b=2 := by linarith
        apply f_solve at this
        subst b
        norm_num

    . have h_cd3 : (b-1)*(b+1) = 0 := by
        linarith
      simp at h_cd3
      rcases h_cd3 with h_cd3 | h_cd3
      . have h_cd4 : b = 1 := by
          linarith

        subst b
        norm_num at *
        have h_cd5 : c = 2 - d := by
          linarith

        rw [h_cd5] at ha
        have h_cd6 : (d-1)^2 = 0 := by
          linarith

        simp at h_cd6
        have h_cd7 : d = 1 := by
          linarith
        subst d c
        simp; norm_num

      . have h_cd4 : b = -1 := by
          linarith

        subst b
        norm_num at *
        have h_cd5 : c = 2 - d := by
          linarith

        rw [h_cd5] at ha
        have h_cd6 : (d+1)*(d-3) = 0 := by
          linarith

        simp at h_cd6
        rcases h_cd6 with h_cd6 | h_cd6
        . have h_cd7 : d = -1 := by
            linarith
          subst d c
          simp; norm_num
        . have h_cd7 : d = 3 := by
            linarith

          subst d c
          simp; norm_num

  . have h_cd1 : c * d = 1 := by
      linarith

    have h_ab3 : a + b = 2 := by
      nlinarith

    rcases h_cd with h_cd2 | h_cd3
    . have h_cd4 : c = d := by
        linarith

      rw [h_cd4] at h_cd1
      have h_cd5 : (d-1)*(d+1) = 0 := by
        linarith

      simp at h_cd5
      rcases h_cd5 with h_cd5 | h_cd5
      . have h_cd6 : d = 1 := by
          linarith
        subst d c
        have h_ab4 : a * b = 1 := by
          linarith

        have h_ab5 : a = 2-b := by
          linarith

        rw [h_ab5] at h_ab4
        have : (b - 1)^2 = 0 := by
          linarith

        simp at this
        have h_ab6 : b = 1 := by
          linarith

        subst b a
        simp; norm_num

      . have h_cd6 : d = -1 := by
          linarith
        subst d c
        have h_ab4 : a * b = -3 := by
          linarith

        have h_ab5 : a = 2-b := by
          linarith

        rw [h_ab5] at h_ab4
        have : (b - 3)*(b+1) = 0 := by
          linarith

        simp at this
        rcases this with this | this
        . have h_ab6 : b = 3 := by
            linarith

          subst b a
          simp; norm_num

        . have h_ab6 : b = -1 := by
            linarith
          subst b a
          simp; norm_num


    . have h_ab4 : a = 2 - b := by
        linarith

      rw [h_ab4] at h_cd3

      have h_ab5 : (b-1)^2 = 0 := by
        linarith

      simp at h_ab5
      have h_ab6 : b = 1 := by
        linarith

      subst b a
      norm_num at *

      have h_cd3 : c = 2 - d := by
        linarith

      rw [h_cd3] at h_cd1
      have h_cd4 : (d-1)^2 = 0 := by
        linarith

      simp at h_cd4
      have h_cd5 : d = 1 := by
        linarith

      subst d c
      simp; norm_num
