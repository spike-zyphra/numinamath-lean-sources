import Mathlib

open Set

set_option maxHeartbeats 500000

-- (3) If a series of functions have the same analytical expression, the same range, but different domains, then these functions are called "functions of the same family". How many "functions of the same family" are there for the function with the analytical expression $y=-x^{2}$ and the range $\{0, -1, -9\}$?

-- (C) 9

theorem algebra_284925
  (f : ℝ → ℝ)
  (hf : f = fun x => -x^2)
  (R : Set ℝ)
  (hR : R = {0, -1, -9}) :
  {I : Set ℝ | f '' I = R} = {{-3, -1, 0}, {-3, 0, 1}, {-1, 0, 3}, {0, 1, 3}, {-3, -1, 0, 1}, {-3, -1, 0, 3}, {-3, 0, 1, 3}, {-1, 0, 1, 3}, {-3, -1, 0, 1, 3}} := by

  ext s
  simp
  constructor
  . intro hx
    unfold image at hx
    rw [hf, hR] at hx
    simp at hx
    let S:= {x | ∃ a ∈ s, -a ^ 2 = x}
    have hS : S = {0, -1, -9} := by unfold S; exact hx
    have h1 : 0 ∈ S := by rw [hS]; simp
    have h2 : -1 ∈ S := by rw [hS]; simp
    have h3 : -9 ∈ S := by rw [hS]; simp

    unfold S at h1 h2 h3
    simp at h1 h2 h3

    replace h3 : ∃ a ∈ s, a = 3 ∨ a = -3 := by
      rcases h3 with ⟨a, ha, h3⟩
      use a
      constructor
      . exact ha
      . have : (a-3) * (a+3) = 0 := by ring_nf; linarith
        simp at this
        rcases this with h | h
        . left; linarith
        . right; linarith

    obtain ⟨a1, ha1, h1⟩ := h2
    obtain ⟨a2, ha2, h2⟩ := h3


    have h4 : s ⊆ ({-3, -1, 0, 1, 3}: Set ℝ) := by
      intro a ha
      have : -a^2 ∈ ({0, -1, -9}: Set ℝ) := by
        rw [←hS]
        use a

      rcases this with h | h | h
      all_goals simp at h ⊢
      all_goals try tauto
      have : (a-3) * (a+3) = 0 := by ring_nf; linarith
      simp at this
      rcases this with h | h
      . have : a = 3 := by linarith
        tauto
      . have : a = -3 := by linarith
        tauto



    by_cases hs1 : -3 ∈ s
    . by_cases hs2 : -1 ∈ s
      . by_cases hs3 : 1 ∈ s
        . by_cases hs4 : 3 ∈ s
          . suffices s = {-3, -1, 0, 1, 3} by tauto
            ext x; simp
            constructor
            . intro hx
              have := h4 hx
              rcases this with rfl | rfl | rfl | rfl | rfl
              all_goals tauto
            . intro hx
              rcases hx with rfl | rfl | rfl | rfl | rfl
              all_goals tauto
          . suffices s = {-3, -1, 0, 1} by tauto
            ext x; simp
            constructor
            . intro hx
              have := h4 hx
              rcases this with rfl | rfl | rfl | rfl | rfl
              all_goals tauto
            . intro hx
              rcases hx with rfl | rfl | rfl | rfl
              all_goals tauto
        . by_cases hs4 : 3 ∈ s
          . suffices s = {-3, -1, 0, 3} by tauto
            ext x; simp
            constructor
            . intro hx
              have := h4 hx
              rcases this with rfl | rfl | rfl | rfl | rfl
              all_goals tauto
            . intro hx
              rcases hx with rfl | rfl | rfl | rfl
              all_goals tauto
          . suffices s = {-3, -1, 0} by tauto
            ext x; simp
            constructor
            . intro hx
              have := h4 hx
              rcases this with rfl | rfl | rfl | rfl | rfl
              all_goals tauto
            . intro hx
              rcases hx with rfl | rfl | rfl
              all_goals tauto
      . have hs3 : 1 ∈ s := by
          rcases h1 with rfl | rfl
          all_goals tauto

        by_cases hs4 : 3 ∈ s
        . suffices s = {-3, 0, 1, 3} by tauto
          ext x; simp
          constructor
          . intro hx
            have := h4 hx
            rcases this with rfl | rfl | rfl | rfl | rfl
            all_goals tauto
          . intro hx
            rcases hx with rfl | rfl | rfl | rfl
            all_goals tauto
        . suffices s = {-3, 0, 1} by tauto
          ext x; simp
          constructor
          . intro hx
            have := h4 hx
            rcases this with rfl | rfl | rfl | rfl | rfl
            all_goals tauto
          . intro hx
            rcases hx with rfl | rfl | rfl
            all_goals tauto

    . have hs2: s ⊆ {-1, 0, 1, 3} := by
        intro x hs
        have := h4 hs
        rcases this with rfl | rfl | rfl | rfl | rfl
        all_goals tauto

      have hs3 : 3 ∈ s := by
        rcases h2 with rfl | rfl
        all_goals tauto

      by_cases hs4 : -1 ∈ s
      . by_cases hs5 : 1 ∈ s
        . suffices s = {-1,0,1,3} by tauto
          ext x; simp
          constructor
          . intro hx
            have := h4 hx
            rcases this with rfl | rfl | rfl | rfl | rfl
            all_goals tauto
          . intro hx
            rcases hx with rfl | rfl | rfl | rfl
            all_goals tauto

        . suffices s = {-1,0,3} by tauto
          ext x; simp
          constructor
          . intro hx
            have := h4 hx
            rcases this with rfl | rfl | rfl | rfl | rfl
            all_goals tauto
          . intro hx
            rcases hx with rfl | rfl | rfl
            all_goals tauto

      . have hs5 : 1 ∈ s := by
          rcases h1 with rfl | rfl
          all_goals tauto

        suffices s = {0,1,3} by tauto
        ext x; simp
        constructor
        . intro hx
          have := h4 hx
          rcases this with rfl | rfl | rfl | rfl | rfl
          all_goals tauto
        . intro hx
          rcases hx with rfl | rfl | rfl
          all_goals tauto

  . intro hx
    rw [hf, hR]
    unfold image
    simp
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
    . norm_num
      ext y
      simp
      tauto
