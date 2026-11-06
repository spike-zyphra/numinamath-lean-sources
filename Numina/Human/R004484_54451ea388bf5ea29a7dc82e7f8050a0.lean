import Mathlib

set_option maxHeartbeats 300000

theorem algebra_273106 {a b c : ℝ}
  (hab : a < b) (hbc : b < c):
    ({a+2*b, a+2*c, b+2*a, b+2*c, c+2*a, c+2*b}: Finset ℝ).card = 4
  ∨ ({a+2*b, a+2*c, b+2*a, b+2*c, c+2*a, c+2*b}: Finset ℝ).card = 6 := by

  let E1 := a + 2 * b
  let E2 := a + 2 * c
  let E3 := b + 2 * a
  let E4 := b + 2 * c
  let E5 := c + 2 * a
  let E6 := c + 2 * b

  let S : Finset ℝ := {E1, E2, E3, E4, E5, E6} 

  have : S.card ≤ 6 := Finset.card_le_six

  have h31: E3 < E1 := by
    unfold E3 E1
    linarith

  have h12: E1 < E2 := by
    unfold E1 E2
    linarith

  have h24: E2 < E4 := by
    unfold E2 E4
    linarith

  have h35: E3 < E5 := by
    unfold E3 E5
    linarith

  have h52: E5 < E2 := by
    unfold E5 E2
    linarith

  have h16: E1 < E6 := by
    unfold E1 E6
    linarith

  have h64: E6 < E4 := by
    unfold E6 E4
    linarith

  have h1: {E3, E1, E2, E4} ⊆ S := by
    unfold S
    have : E3 ∈ ({E3, E1, E2, E4}: Finset ℝ) := by simp
    intro e he
    simp at he
    rcases he with rfl | rfl | rfl | rfl
    all_goals simp

  have h2: ({E3, E1, E2, E4}: Finset ℝ).card = 4 := by
    rw [Finset.card_eq_succ]
    use E3, ({E1, E2, E4}: Finset ℝ)
    refine ⟨?_, ?_, ?_⟩
    . simp
      refine ⟨?_, ?_, ?_⟩
      all_goals linarith
    . simp
    . rw [Finset.card_eq_three]
      use E1, E2, E4
      refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try linarith
      rfl

  have h3: 4 ≤ S.card := by
    rw [← h2]
    apply Finset.card_mono
    exact h1
  

  by_cases h15: E5 = E1
  . left
    have : c + 2 * a = a + 2 * b := by
      unfold E1 E5 at h15
      exact h15

    have : a = 2*b - c := by linarith

    have h26: E6 = E2 := by
      unfold E2 E6
      linarith
    
    have : S = {E3, E1, E2, E4} := by
      ext x
      unfold S
      rw [h26, h15]
      simp
      constructor
      . intro h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try simp

      . intro h
        tauto

    rw [← this] at h2
    unfold S at h2
    exact h2

  . right

    have h26: E6 ≠ E2 := by
      by_contra h
      unfold E2 E6 at h
      unfold E1 E5 at h15

      have : a = 2*b - c := by linarith
      subst a
      contrapose h15
      simp
      linarith

    have h56 : E5 ≠ E6 := by
      by_contra h
      unfold E5 E6 at h
      linarith

    suffices S.card = 6 by
      unfold S at this
      exact this
    
    rw [Finset.card_eq_succ]
    unfold S
    use E5, ({E3, E1, E2, E4, E6}: Finset ℝ)
    refine ⟨?_, ?_, ?_⟩
    . intro h
      simp at h
      rcases h with h1 | h2 | h3 | h4 | h5
      all_goals try linarith
      all_goals contradiction   

    . ext x
      simp
      constructor
      . intro h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp
      . intro h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try simp

    . rw [Finset.card_eq_succ]
      use E6, ({E3, E1, E2, E4}: Finset ℝ)
      refine ⟨?_, ?_, ?_⟩
      . intro h
        simp at h
        rcases h with h1 | h2 | h3 | h4
        all_goals try linarith
        all_goals contradiction
      . ext x
        simp
        constructor
        . intro h
          rcases h with rfl | rfl | rfl | rfl | rfl | rfl
          all_goals try simp
        . intro h
          tauto
      . exact h2

