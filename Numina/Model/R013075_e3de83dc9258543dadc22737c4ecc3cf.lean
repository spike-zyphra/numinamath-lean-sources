import Mathlib

theorem algebra_14030 {f : ℕ+ → ℕ+} (h : ∀ x y, f (x + y) = f x + f y + x * y)
    (h1 : f 1 = 1) : f 25 = 325 := by

  have eq2 : f 2 = 3 := by
    specialize h 1 1 
    rw [show (1 : ℕ+ ) + (1 : ℕ+ ) = (2 : ℕ+ ) by rfl] at h
    rw [h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq3 : f 3 = 6 := by 
    specialize h 2 1 
    rw [show (2 : ℕ+ ) + (1 : ℕ+ ) = (3 : ℕ+ ) by rfl] at h 
    rw [eq2, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq4 : f 4 = 10 := by 
    specialize h 2 2 
    rw [show (2 : ℕ+ ) + (2 : ℕ+ ) = (4 : ℕ+ ) by rfl] at h 
    rw [eq2] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq5 : f 5 = 15 := by 
    specialize h 4 1 
    rw [show (4 : ℕ+ ) + (1 : ℕ+ ) = (5 : ℕ+ ) by rfl] at h 
    rw [eq4, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq6 : f 6 = 21 := by 
    specialize h 5 1 
    rw [show (5 : ℕ+ ) + (1 : ℕ+ ) = (6 : ℕ+ ) by rfl] at h 
    rw [eq5, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq7 : f 7 = 28 := by 
    specialize h 6 1 
    rw [show (6 : ℕ+ ) + (1 : ℕ+ ) = (7 : ℕ+ ) by rfl] at h 
    rw [eq6, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq8 : f 8 = 36 := by 
    specialize h 7 1 
    rw [show (7 : ℕ+ ) + (1 : ℕ+ ) = (8 : ℕ+ ) by rfl] at h 
    rw [eq7, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq9 : f 9 = 45 := by 
    specialize h 8 1 
    rw [show (8 : ℕ+ ) + (1 : ℕ+ ) = (9 : ℕ+ ) by rfl] at h 
    rw [eq8, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq10 : f 10 = 55 := by 
    specialize h 9 1 
    rw [show (9 : ℕ+ ) + (1 : ℕ+ ) = (10 : ℕ+ ) by rfl] at h 
    rw [eq9, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq11 : f 11 = 66 := by 
    specialize h 10 1 
    rw [show (10 : ℕ+ ) + (1 : ℕ+ ) = (11 : ℕ+ ) by rfl] at h 
    rw [eq10, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq12 : f 12 = 78 := by 
    specialize h 11 1 
    rw [show (11 : ℕ+ ) + (1 : ℕ+ ) = (12 : ℕ+ ) by rfl] at h 
    rw [eq11, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq13 : f 13 = 91 := by 
    specialize h 12 1 
    rw [show (12 : ℕ+ ) + (1 : ℕ+ ) = (13 : ℕ+ ) by rfl] at h 
    rw [eq12, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq14 : f 14 = 105 := by 
    specialize h 13 1 
    rw [show (13 : ℕ+ ) + (1 : ℕ+ ) = (14 : ℕ+ ) by rfl] at h 
    rw [eq13, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq15 : f 15 = 120 := by 
    specialize h 14 1 
    rw [show (14 : ℕ+ ) + (1 : ℕ+ ) = (15 : ℕ+ ) by rfl] at h 
    rw [eq14, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq16 : f 16 = 136 := by 
    specialize h 15 1 
    rw [show (15 : ℕ+ ) + (1 : ℕ+ ) = (16 : ℕ+ ) by rfl] at h 
    rw [eq15, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq17 : f 17 = 153 := by 
    specialize h 16 1 
    rw [show (16 : ℕ+ ) + (1 : ℕ+ ) = (17 : ℕ+ ) by rfl] at h 
    rw [eq16, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq18 : f 18 = 171 := by 
    specialize h 17 1 
    rw [show (17 : ℕ+ ) + (1 : ℕ+ ) = (18 : ℕ+ ) by rfl] at h 
    rw [eq17, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq19 : f 19 = 190 := by 
    specialize h 18 1 
    rw [show (18 : ℕ+ ) + (1 : ℕ+ ) = (19 : ℕ+ ) by rfl] at h 
    rw [eq18, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq20 : f 20 = 210 := by 
    specialize h 19 1 
    rw [show (19 : ℕ+ ) + (1 : ℕ+ ) = (20 : ℕ+ ) by rfl] at h 
    rw [eq19, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq21 : f 21 = 231 := by 
    specialize h 20 1 
    rw [show (20 : ℕ+ ) + (1 : ℕ+ ) = (21 : ℕ+ ) by rfl] at h 
    rw [eq20, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq22 : f 22 = 253 := by 
    specialize h 21 1 
    rw [show (21 : ℕ+ ) + (1 : ℕ+ ) = (22 : ℕ+ ) by rfl] at h 
    rw [eq21, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq23 : f 23 = 276 := by 
    specialize h 22 1 
    rw [show (22 : ℕ+ ) + (1 : ℕ+ ) = (23 : ℕ+ ) by rfl] at h 
    rw [eq22, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq24 : f 24 = 300 := by 
    specialize h 23 1 
    rw [show (23 : ℕ+ ) + (1 : ℕ+ ) = (24 : ℕ+ ) by rfl] at h 
    rw [eq23, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  have eq25 : f 25 = 325 := by 
    specialize h 24 1 
    rw [show (24 : ℕ+ ) + (1 : ℕ+ ) = (25 : ℕ+ ) by rfl] at h 
    rw [eq24, h1] at h 
    norm_num at h ⊢ 
    exact_mod_cast h

  exact_mod_cast eq25