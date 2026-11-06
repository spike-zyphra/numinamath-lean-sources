import Mathlib

theorem algebra_2846 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (h : a + b + c = 2013) (op : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ))
    (h_op : ∀ x y z, op (x, y, z) = (y + z - x, x + z - y, x + y - z)) :
    ∃ a' b' c' : ℤ, (a', b', c') = op^[10] (a, b, c) ∧ (a' < 0 ∨ b' < 0 ∨ c' < 0) := by

  use (op^[10] (a, b, c)).1, (op^[10] (a, b, c)).2.1, (op^[10] (a, b, c)).2.2
  constructor 
  · -- Show the equality of triples.
    rfl 
  · -- Show that at least one is negative 
    by_contra h'
    push_neg at h'

    have h4 : (op^[10] (a, b, c)).1 + (op^[10] (a, b, c)).2.1 + (op^[10] (a, b, c)).2.2 = 2013 := by 
      have h1 : ∀ (n : ℕ), (op^[n] (a, b, c)).1 + (op^[n] (a, b, c)).2.1 + (op^[n] (a, b, c)).2.2 = 2013 := by 
        intro n 
        induction n with 
        | zero => 
          simp [h]
        | succ n ih => 
          simp [Function.iterate_succ_apply', h_op] at ih ⊢ 
          ring_nf at ih ⊢ 
          omega 
      specialize h1 10 
      simpa using h1

    have h5 : (op^[10] (a, b, c)).1 ≥ 0 := by 
      omega 
    have h6 : (op^[10] (a, b, c)).2.1 ≥ 0 := by 
      omega 
    have h7 : (op^[10] (a, b, c)).2.2 ≥ 0 := by 
      omega

    -- Substitute all at appropriate system.
    simp [Function.iterate_succ_apply', h_op] at h4 h5 h6 h7 ⊢ 
    all_goals 
      omega