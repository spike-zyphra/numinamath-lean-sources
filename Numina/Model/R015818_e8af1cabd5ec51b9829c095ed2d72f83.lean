import Mathlib

theorem algebra_157515 {u : ℕ → ℝ} (hu : ∀ n, u (n + 1) = -1 / (u n + 1)) (ha : u 1 > 0) :
    u 16 = u 1 := by
  have h1 : u 2 = -1 / (u 1 + 1) := by 
    specialize hu 1
    simpa using hu

  have h2 : u 3 = -1 / (u 2 + 1) := by
    specialize hu 2
    simpa using hu

  have h3 : u 4 = -1 / (u 3 + 1) := by
    specialize hu 3
    simpa using hu

  have h4 : u 5 = -1 / (u 4 + 1) := by
    specialize hu 4
    simpa using hu

  have h5 : u 6 = -1 / (u 5 + 1) := by
    specialize hu 5
    simpa using hu

  have h6 : u 7 = -1 / (u 6 + 1) := by
    specialize hu 6
    simpa using hu

  have h7 : u 8 = -1 / (u 7 + 1) := by
    specialize hu 7
    simpa using hu

  have h8 : u 9 = -1 / (u 8 + 1) := by
    specialize hu 8
    simpa using hu

  have h9 : u 10 = -1 / (u 9 + 1) := by
    specialize hu 9
    simpa using hu

  have h10 : u 11 = -1 / (u 10 + 1) := by
    specialize hu 10
    simpa using hu

  have h11 : u 12 = -1 / (u 11 + 1) := by
    specialize hu 11
    simpa using hu

  have h12 : u 13 = -1 / (u 12 + 1) := by
    specialize hu 12
    simpa using hu

  have h13 : u 14 = -1 / (u 13 + 1) := by
    specialize hu 13
    simpa using hu

  have h14 : u 15 = -1 / (u 14 + 1) := by
    specialize hu 14
    simpa using hu

  have h15 : u 16 = -1 / (u 15 + 1) := by
    specialize hu 15
    simpa using hu
  
  -- Now express u 16 in terms of u 1
  rw [h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1]
  -- We have a cycle of 3 steps yielding u4 = u1.
  -- The substitutions will yield a function of u1, which needs to be shown equal to u1.
  -- To simplify, we have to show u 1 satisfies equation u4 = u1.
  -- This is that (a+1)/a=a implies a^2=a+1.
  -- Since we have such algebra, combine these equalities with computation.
  have ha1ne : u 1 + 1 ≠ 0 := by linarith
  have ha2ne : u 1 ≠ 0 := by linarith
  field_simp [ha1ne, ha2ne]
  <;> ring_nf <;> field_simp [ha1ne, ha2ne]
  <;> nlinarith
  <;> try { nlinarith }
  <;> try { tauto }
  <;> ring_nf
  <;> try { tauto }
  <;> try { nlinarith }
  <;> try { ring_nf <;> nlinarith }
  <;> try { tauto }
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals try { nlinarith }
  all_goals try { nlinarith }
  all_goals try { tauto }
  all_goals try { nlinarith }
  all_goals try { nlinarith }
  all_goals try { tauto }