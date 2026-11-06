import Mathlib

theorem algebra_282921 {a : ℕ → ℤ} (ha : ∀ n, a (n + 1) = 2 * a n + 2 ^ n - 1)
    (h : ∃ d, ∀ n, (a n + d) / 2 ^ n = (a 0 + d) / 2 ^ 0 + d * n) :
    d = -1 := by
  rcases h with ⟨d, hd⟩
  have eq1 := hd 0 
  norm_num at eq1 
  have eq2 := hd 1 
  norm_num at eq2 
  have eq3 := hd 2 
  norm_num at eq3 
  have eq4 := hd 3 
  norm_num at eq4 
  have eq5 := hd 4 
  norm_num at eq5 
  have eq6 := hd 5 
  norm_num at eq6 
  -- Derive expressions for a 1, ..., a 5
  have eq7 : a 1 = 2 * a 0 + 2 ^ 0 - 1 := by
    specialize ha 0 
    simpa using ha 
  have eq8 : a 2 = 2 * a 1 + 2 ^ 1 - 1 := by 
    specialize ha 1 
    simpa using ha 
  have eq9 : a 3 = 2 * a 2 + 2 ^ 2 - 1 := by 
    specialize ha 2 
    simpa using ha 
  have eq10 : a 4 = 2 * a 3 + 2 ^ 3 - 1 := by 
    specialize ha 3 
    simpa using ha 
  have eq11 : a 5 = 2 * a 4 + 2 ^ 4 - 1 := by 
    specialize ha 4 
    simpa using ha 
  -- Express a 1, ..., a 5 in terms of a 0
  -- Note that eq7 gives expression for a 1
  -- From eq8 and eq7
  have eq14 : a 2 = 4 * a 0 + 1 := by
    rw [eq8, eq7]
    all_goals 
      omega 
  have eq15 : a 3 = 8 * a 0 + 3 := by
    rw [eq9, eq14]
    all_goals 
      omega 
  have eq16 : a 4 = 16 * a 0 + 7 := by 
    rw [eq10, eq15]
    all_goals 
      omega 
  have eq17 : a 5 = 32 * a 0 + 15 := by 
    rw [eq11, eq16]
    all_goals 
      omega 
  omega