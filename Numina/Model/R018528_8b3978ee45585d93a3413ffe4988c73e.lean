import Mathlib

theorem algebra_249059 {z : ℂ} (hz : z ≠ 0) (h : z + 1 / z = 1) :
    z ^ 1993 + z ^ 1994 + z ^ 1995 + z ^ 1996 + z ^ 1997 = -1 := by
  have h1 : z ^ 2 - z + 1 = 0 := by
    have h2 : z ≠ 0 := hz
    have eq1 : z + 1 / z = 1 := h
    have eq2 : z ^ 2 + 1 = z := by
      calc
        z ^ 2 + 1 = z * (z + 1 / z) := by 
          field_simp [h2]
          <;> ring
        _ = z * 1 := by rw [h]
        _ = z := by ring
    have eq3 : z ^ 2 - z + 1 = 0 := by 
      calc
        z ^ 2 - z + 1 = (z ^ 2 + 1) - z := by ring
        _ = z - z := by rw [eq2]
        _ = 0 := by ring
    exact eq3
  have h2 : z ^ 2 = z - 1 := by
    calc
      z ^ 2 = z ^ 2 - z + 1 + z - 1 := by ring
      _ = 0 + z - 1 := by rw [h1]
      _ = z - 1 := by ring
  -- Prove z^3 = -1
  have h3 : z^3 = -1 := by
    calc 
      z ^ 3 = z * z^2 := by ring 
      _ = z * (z - 1) := by rw [h2]
      _ = z^2 - z := by ring
      _ = (z - 1) - z := by rw [h2]
      _ = -1 := by ring
  -- Prove z^4 = -z
  have h4 : z ^ 4 = -z := by
    calc 
      z ^ 4 = z * z^3 := by ring 
      _ = z * (-1) := by rw [h3]
      _ = -z := by ring
  -- Prove z^5 = -z + 1
  have h5 : z ^ 5 = -z + 1 := by
    calc 
      z ^ 5 = z * z^4 := by ring 
      _ = z * (-z) := by rw [h4]
      _ = -z^2 := by ring
      _ = -(z - 1) := by rw [h2]
      _ = -z + 1 := by ring
  -- Prove z^6 = 1
  have h6 : z ^ 6 = 1 := by
    calc 
      z ^ 6 = z * z^5 := by ring 
      _ = z * (-z + 1) := by rw [h5]
      _ = -z^2 + z := by ring
      _ = -(z - 1) + z := by rw [h2]
      _ = -z + 1 + z := by ring
      _ = 1 := by ring 
  have h7 : z ^ 1993 = z := by 
    have h8 : ∀ n : ℕ, z ^ (6 * n + 1) = z := by
      intro n 
      induction n with 
      | zero =>
        simp 
        <;> ring 
      | succ n ih =>
        calc 
          z ^ (6 * (n + 1) + 1) = z ^ (6 * n + 1 + 6) := by ring_nf 
          _ = (z ^ (6 * n + 1)) * (z ^ 6) := by ring
          _ = z * 1 := by 
            rw [ih]
            <;> rw [h6]
            all_goals ring_nf 
            all_goals tauto
          _ = z := by ring 
    specialize h8 332
    norm_num at h8 ⊢
    all_goals try simp [h8]
    all_goals try linarith
  -- Prove z^1994 = z ^ 2
  have h8 : z ^ 1994 = z ^ 2 := by 
    have h9 : ∀ n : ℕ, z ^ (6 * n + 2) = z ^ 2 := by
      intro n 
      induction n with 
      | zero =>
        simp 
        <;> ring 
      | succ n ih =>
        calc 
          z ^ (6 * (n + 1) + 2) = z ^ (6 * n + 2 + 6) := by ring_nf 
          _ = (z ^ (6 * n + 2)) * (z ^ 6) := by ring
          _ = z ^ 2 * 1 := by 
            rw [ih]
            <;> rw [h6]
            all_goals ring_nf 
            all_goals tauto
          _ = z ^ 2 := by ring 
    specialize h9 332
    norm_num at h9 ⊢
    all_goals try simp [h9]
    all_goals try linarith
  -- Prove z^1995 = z ^ 3
  have h9 : z ^ 1995 = z ^ 3 := by 
    have h10 : ∀ n : ℕ, z ^ (6 * n + 3) = z ^ 3 := by
      intro n 
      induction n with 
      | zero =>
        simp 
        <;> ring 
      | succ n ih =>
        calc 
          z ^ (6 * (n + 1) + 3) = z ^ (6 * n + 3 + 6) := by ring_nf 
          _ = (z ^ (6 * n + 3)) * (z ^ 6) := by ring
          _ = z ^ 3 * 1 := by 
            rw [ih]
            <;> rw [h6]
            all_goals ring_nf 
            all_goals tauto
          _ = z ^ 3 := by ring 
    specialize h10 332
    norm_num at h10 ⊢
    all_goals try simp [h10]
    all_goals try linarith
  -- Prove z^1996 = z ^ 4
  have h10 : z ^ 1996 = z ^ 4 := by 
    have h11 : ∀ n : ℕ, z ^ (6 * n + 4) = z ^ 4 := by
      intro n 
      induction n with 
      | zero =>
        simp 
        <;> ring 
      | succ n ih =>
        calc 
          z ^ (6 * (n + 1) + 4) = z ^ (6 * n + 4 + 6) := by ring_nf 
          _ = (z ^ (6 * n + 4)) * (z ^ 6) := by ring
          _ = z ^ 4 * 1 := by 
            rw [ih]
            <;> rw [h6]
            all_goals ring_nf 
            all_goals tauto
          _ = z ^ 4 := by ring 
    specialize h11 332
    norm_num at h11 ⊢
    all_goals try simp [h11]
    all_goals try linarith
  -- Prove z^1997 = z ^ 5
  have h11 : z ^ 1997 = z ^ 5 := by 
    have h12 : ∀ n : ℕ, z ^ (6 * n + 5) = z ^ 5 := by
      intro n 
      induction n with 
      | zero =>
        simp 
        <;> ring 
      | succ n ih =>
        calc 
          z ^ (6 * (n + 1) + 5) = z ^ (6 * n + 5 + 6) := by ring_nf 
          _ = (z ^ (6 * n + 5)) * (z ^ 6) := by ring
          _ = z ^ 5 * 1 := by 
            rw [ih]
            <;> rw [h6]
            all_goals ring_nf 
            all_goals tauto
          _ = z ^ 5 := by ring 
    specialize h12 332
    norm_num at h12 ⊢
    all_goals try simp [h12]
    all_goals try linarith
  rw [h7, h8, h9, h10, h11]
  rw [h2, h3, h4, h5]
  ring_nf
  <;> norm_num [h1, h2, h3, h4, h5, h6]
  <;> ring_nf 
  <;> norm_num
  all_goals try assumption