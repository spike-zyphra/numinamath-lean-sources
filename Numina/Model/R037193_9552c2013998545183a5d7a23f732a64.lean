import Mathlib

theorem calculus_21984 (P L : Set (Fin 3 → ℝ))
    (hP : P = {v | ∃ t s : ℝ, v = ![1, 6, 7] + s • ![2, -1, -1] + t • ![2, -3, -5]})
    (hL : L = {w | ∃ u : ℝ, w = ![7, 4, 1] + u • ![3, 0, -1]}) :
    P ∩ L = {![1, 4, 3]} := by 
  ext x 
  simp [hP, hL]
  constructor
  · -- Assume x ∈ P ∩ L, prove x ∈ {![1, 4, 3]}
    rintro ⟨⟨t, s, hp⟩, ⟨u, hl⟩⟩
    have eq1 := congr_arg (λ f => f 0) hp
    have eq2 := congr_arg (λ f => f 1) hp
    have eq3 := congr_arg (λ f => f 2) hp
    have eq4 := congr_arg (λ f => f 0) hl
    have eq5 := congr_arg (λ f => f 1) hl
    have eq6 := congr_arg (λ f => f 2) hl
    simp [Fin.sum_univ_three] at eq1 eq2 eq3 eq4 eq5 eq6 
    have ht : t = 1 := by 
      nlinarith 
    have hs : s = -1 := by 
      nlinarith 
    have hu : u = -2 := by 
      nlinarith 
    funext i 
    fin_cases i 
    · -- i = 0
      have h0 : x 0 = 1 := by
        have h1 : x 0 = 1 + s * 2 + t * 2 := by 
          linarith [eq1]
        rw [ht, hs] at h1 
        linarith 
      simpa using h0 
    · -- i = 1
      have h1 : x 1 = 4 := by
        have eq7 : x 1 = 6 + -s + -(t * 3) := by
          linarith [eq2]
        rw [hs, ht] at eq7 
        linarith 
      simpa using h1 
    · -- i = 2 
      have h2 : x 2 = 3 := by
        have eq8 : x 2 = 7 + -s + -(t * 5) := by 
          linarith [eq3] 
        rw [hs, ht] at eq8 
        linarith 
      simpa using h2
  · -- Assume x ∈ {![1, 4, 3]}, prove x ∈ P ∩ L
    intro hx
    have hx0 : x 0 = 1 := by 
      simpa using congr_arg (λ f => f 0) hx 
    have hx1 : x 1 = 4 := by 
      simpa using congr_arg (λ f => f 1) hx 
    have hx2 : x 2 = 3 := by 
      simpa using congr_arg (λ f => f 2) hx 
    constructor
    · -- Show x ∈ P 
      use 1, -1 
      funext i 
      fin_cases i 
      · -- i = 0
        simp [hx0]
        all_goals norm_num 
      · -- i = 1 
        simp [hx1]
        all_goals norm_num 
      · -- i = 2 
        simp [hx2]
        all_goals norm_num 
    · -- Show x ∈ L 
      use -2 
      funext i 
      fin_cases i 
      · -- i = 0 
        simp [hx0]
        all_goals norm_num 
      · -- i = 1 
        simp [hx1]
        all_goals norm_num 
      · -- i = 2 
        simp [hx2]
        all_goals norm_num