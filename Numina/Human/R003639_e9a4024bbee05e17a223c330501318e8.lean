import Mathlib

-- 18. (2004 Australian Mathematical Olympiad) Find all quadruples of real numbers $(a, b, c, d)$ such that:
-- the sum of the product of any three of the numbers and the remaining one is the same, regardless of the choice of the three numbers.

theorem algebra_203384 (a b c d : ℝ) :
    a + b * c * d = b + a * c * d
  ∧ b + a * c * d = c + a * b * d
  ∧ c + a * b * d = d + a * b * c
  ↔
  (a, b, c, d) ∈
  {p | ∃ r : ℝ, p = (r, r, r, r)} ∪
  {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (t, t, t, r)} ∪
  {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (t, t, r, t)} ∪
  {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (t, r, t, t)} ∪
  {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (r, t, t, t)} ∪
  {p | ∃ r : ℝ, r ≠ 0 ∧ p = (r, r, 1/r, 1/r)} ∪
  {p | ∃ r : ℝ, r ≠ 0 ∧ p = (r, 1/r, r, 1/r)} ∪
  {p | ∃ r : ℝ, r ≠ 0 ∧ p = (r, 1/r, 1/r, r)}
   := by

  let S1 := {p | ∃ r : ℝ, p = (r, r, r, r)}
  let T1 := {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (t, t, t, r)}
  let T2 := {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (t, t, r, t)}
  let T3 := {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (t, r, t, t)}
  let T4 := {p | ∃ (t r : ℝ), (t = 1 ∨ t = -1) ∧ p = (r, t, t, t)}

  let U1 := {p | ∃ r : ℝ, r ≠ 0 ∧ p = (r, r, 1/r, 1/r)}
  let U2 := {p | ∃ r : ℝ, r ≠ 0 ∧ p = (r, 1/r, r, 1/r)}
  let U3 := {p | ∃ r : ℝ, r ≠ 0 ∧ p = (r, 1/r, 1/r, r)}


  refine Iff.intro ?_ $ by
    intro h
    rw [Set.mem_union] at h; rcases h with h | h
    . rw [Set.mem_union] at h; rcases h with h | h
      . rw [Set.mem_union] at h; rcases h with h | h
        . rw [Set.mem_union] at h; rcases h with h | h
          . rw [Set.mem_union] at h; rcases h with h | h
            . rw [Set.mem_union] at h; rcases h with h | h
              . rw [Set.mem_union] at h; rcases h with h | h
                . simp at h
                  have := h.1
                  have := h.2.1
                  have := h.2.2
                  subst b c d
                  simp
                . simp at h
                  rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩
                  all_goals subst a b c; simp; linarith
              . simp at h
                rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩
                all_goals subst a b d; simp; constructor
                all_goals linarith
            . simp at h
              rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩
              all_goals subst a c d; simp; constructor
              all_goals linarith
          . simp at h
            rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩
            all_goals subst b c d; simp; linarith
        . simp at h
          -- have ⟨h1,h2,h3,h4⟩ := h
          obtain ⟨r,⟨hr1,hr2,hr3,hr4,hr5⟩⟩ := h
          subst a b c d
          field_simp
          linarith
      . simp at h
        -- have ⟨h1,h2,h3,h4⟩ := h
        obtain ⟨r,⟨hr1,hr2,hr3,hr4,hr5⟩⟩ := h
        subst a b c d
        field_simp
        refine ⟨?_,?_,?_⟩
        all_goals linarith
    . simp at h
      -- have ⟨h1,h2,h3,h4⟩ := h
      obtain ⟨r,⟨hr1,hr2,hr3,hr4,hr5⟩⟩ := h
      subst a b c d
      field_simp
      refine ⟨?_,?_⟩
      all_goals linarith

  intro hx
  repeat rw [Set.mem_union]
  by_cases ha1: b = a ∧ c = a ∧ d = a
  . suffices (a, b, c, d) ∈ {p | ∃ r, p = (r, r, r, r)} by
      left; left; left; left; left; left; left; exact this
    simp
    exact ha1

  by_cases ht1: b = a ∧ c = a ∧ d ≠ a
  . have ⟨ h1, h2, h3 ⟩ := ht1
    have : (a,b,c,d) ∈ T1 := by
      subst b c
      ring_nf at hx
      simp at hx
      have : (a^2 - 1) * (d-a) = 0 := by linarith
      simp at this
      rcases this with h | h
      . have : (a-1)*(a+1)=0 := by linarith
        simp at this
        rcases this with h | h
        . have : a = 1 := by linarith
          subst a
          unfold T1
          simp
        . have : a = -1 := by linarith
          subst a
          unfold T1
          simp
      . have : d = a := by linarith
        contradiction

    unfold T1 at this
    left; left; left; left; left; left; right; exact this

  by_cases ht2: b = a ∧ d = a ∧ c ≠ a
  . have ⟨ h1, h2, h3 ⟩ := ht2
    have : (a,b,c,d) ∈ T2 := by
      subst b d
      ring_nf at hx
      simp at hx
      have : (a^2 - 1) * (c-a) = 0 := by linarith
      simp at this
      rcases this with h | h
      . have : (a-1)*(a+1)=0 := by linarith
        simp at this
        rcases this with h | h
        . have : a = 1 := by linarith
          subst a
          unfold T2
          simp
        . have : a = -1 := by linarith
          subst a
          unfold T2
          simp
      . have : c = a := by linarith
        contradiction

    unfold T2 at this
    left; left; left; left; left; right; exact this

  by_cases ht3: c = a ∧ d = a ∧ b ≠ a
  . have ⟨ h1, h2, h3 ⟩ := ht3
    have : (a,b,c,d) ∈ T3 := by
      subst c d
      ring_nf at hx
      simp at hx
      have : (a^2 - 1) * (b-a) = 0 := by linarith
      simp at this
      rcases this with h | h
      . have : (a-1)*(a+1)=0 := by linarith
        simp at this
        rcases this with h | h
        . have : a = 1 := by linarith
          subst a
          unfold T3
          simp
        . have : a = -1 := by linarith
          subst a
          unfold T3
          simp
      . have : b = a := by linarith
        contradiction
    unfold T3 at this
    left; left; left; left; right; exact this

  by_cases ht4: c = b ∧ d = b ∧ b ≠ a
  . have ⟨ h1, h2, h3 ⟩ := ht4
    have : (a,b,c,d) ∈ T4 := by
      subst c d
      ring_nf at hx
      simp at hx
      have : (b^2 - 1) * (a-b) = 0 := by linarith
      simp at this
      rcases this with h | h
      . have : (b-1)*(b+1)=0 := by linarith
        simp at this
        rcases this with h | h
        . have : b = 1 := by linarith
          subst b
          unfold T4
          simp
        . have : b = -1 := by linarith
          subst b
          unfold T4
          simp
      . have : b = a := by linarith
        contradiction

    unfold T4 at this
    left; left; left; right; exact this

  have ⟨ hx1, hx2, hx3 ⟩ := hx
  have h_solve_ab: b≠a → c*d=1 := by
    intro h
    have : (b-a) * (c*d - 1) = 0:= by linarith
    simp at this
    rcases this with h | h
    . have : b = a := by linarith
      contradiction
    . linarith

  have h_solve_bc: c≠b → a*d=1 := by
    intro h
    have : (c-b) * (a*d - 1) = 0:= by linarith
    simp at this
    rcases this with h | h
    . have : c = b := by linarith
      contradiction
    . linarith

  have h_solve_cd: d≠c → a*b=1 := by
    intro h
    have : (d-c) * (a*b - 1) = 0:= by linarith
    simp at this
    rcases this with h | h
    . have : d = c := by linarith
      contradiction
    . linarith

  have h_solve_ad: d≠a → b*c=1 := by
    intro h
    have : (d-a) * (b*c - 1) = 0:= by linarith
    simp at this
    rcases this with h | h
    . have : d = a := by linarith
      contradiction
    . linarith

  have h_solve_bd: d≠b → a*c=1 := by
    intro h
    have : (d-b) * (a*c - 1) = 0:= by linarith
    simp at this
    rcases this with h | h
    . have : d = b := by linarith
      contradiction
    . linarith

  have h_solve_ac: c≠a → b*d=1 := by
    intro h
    have : (c-a) * (b*d - 1) = 0:= by linarith
    simp at this
    rcases this with h | h
    . have : c = a := by linarith
      contradiction
    . linarith

  by_cases hu1: b = a ∧ d = c ∧ c ≠ b
  . have ⟨ h1, h2, h3 ⟩ := hu1
    have : (a,b,c,d) ∈ U1 := by
      have had_mul: a*d=1 := h_solve_bc h3
      have hbc_mul: b*c=1 := by rw [h1, ← h2]; exact had_mul
      have : a≠0 := by
        intro h
        rw [h] at had_mul
        norm_num at had_mul
      unfold U1
      simp
      use a
      refine ⟨?_,?_,?_,?_,?_⟩
      . intro h
        rw [h] at had_mul
        norm_num at had_mul
      . rfl
      . exact h1
      . field_simp
        rw [<- h1]
        linarith
      . field_simp
        linarith

    unfold U1 at this
    left; left; right; exact this


  by_cases hu2: c = a ∧ d = b ∧ b ≠ a
  . have ⟨ h1, h2, h3 ⟩ := hu2
    have : (a,b,c,d) ∈ U2 := by
      have hcd_mul: c*d=1 := h_solve_ab h3
      have hab_mul: a*b=1 := by rw [← h1, ← h2]; exact hcd_mul
      have : a≠0 := by
        intro h
        rw [h] at hab_mul
        norm_num at hab_mul
      unfold U2
      simp
      use a
      refine ⟨?_,?_,?_,?_,?_⟩
      . exact this
      . rfl
      . field_simp
        linarith
      . exact h1
      . field_simp
        rw [h2]
        linarith


    unfold U2 at this
    left; right; exact this

  by_cases hu3: d = a ∧ c = b ∧ b ≠ a
  . have ⟨ h1, h2, h3 ⟩ := hu3
    have : (a,b,c,d) ∈ U3 := by
      have hcd_mul: c*d=1 := h_solve_ab h3
      have hab_mul: a*b=1 := by rw [← h1, ← h2]; linarith
      have : a≠0 := by
        intro h
        rw [h] at hab_mul
        norm_num at hab_mul
      unfold U3
      simp
      use a
      refine ⟨?_,?_,?_,?_,?_⟩
      . exact this
      . rfl
      . field_simp
        linarith
      . field_simp
        rw [h2]
        linarith
      . exact h1

    unfold U3 at this
    right; exact this

  simp at ha1 ht1 ht2 ht3 ht4 hu1 hu2 hu3

  by_cases hab : b = a
  . have hac: c ≠ a := by
      intro h
      have := ha1 hab h
      have := ht1 hab h
      contradiction

    have hcd: d ≠ c := by
      intro h
      have := hu1 hab h
      have : c = a := by linarith
      contradiction

    have hab_mul: a*b=1 := h_solve_cd hcd
    have hbd_mul: b*d=1 := h_solve_ac hac
    have : b*(a-d)=0 := by linarith
    simp at this
    rcases this with h | h
    . rw [h] at hab_mul
      norm_num at hab_mul
    . have : d = a := by linarith
      have := ht2 hab this
      contradiction

  simp at hab
  have hcd_mul: c*d=1 := h_solve_ab hab

  by_cases hbc : c = b
  . have hbd: d ≠ b := by
      intro h
      have := ht4 hbc h
      contradiction

    have hac_mul: a*c=1 := h_solve_bd hbd
    have : (a-d)*c=0 := by linarith
    simp at this
    rcases this with h | h
    . have : d = a := by linarith
      have := hu3 this hbc
      contradiction
    . rw [h] at hcd_mul
      norm_num at hcd_mul

  simp at hbc
  have had_mul: a*d = 1 := h_solve_bc hbc

  have : (a-c)*d=0 := by linarith
  simp at this
  rcases this with h | h
  . have : c = a := by linarith
    by_cases hbd : d = b
    . have := hu2 this hbd
      contradiction
    . have hac_mul : a*c=1 := h_solve_bd hbd
      have : (a-d)*c=0 := by linarith
      simp at this
      rcases this with h | h
      . have : d = a := by linarith
        have := ht3 (by linarith) this
        contradiction
      . have : c = 0 := by linarith
        rw [h] at hcd_mul
        norm_num at hcd_mul

  . rw [h] at hcd_mul
    norm_num at hcd_mul
