import Mathlib

-- we show a lemma about factoring the equation, which will be used in the proof
lemma lemma_1 (x y z: ℂ) (h: x * (x - 1) + 2 * y * z = y * (y - 1) + 2 * z * x): 
   (x - y) * (y - z - (z - x) - 1) = 0 := by
    replace h: x * (x - 1) + 2 * y * z - (y * (y - 1) + 2 * z * x) = 0 := by
      rw [h]
      ring
    rw [show x * (x - 1) + 2 * y * z - (y * (y - 1) + 2 * z * x) 
      = (x - y) * (y - z - (z - x) - 1) by ring] at h
    exact h
    
/-The set of triples T=(x−y,y−z,z−x) (where x,y,z are complex numbers) that satisfy the system of equations
x(x−1)+2yz=y(y−1)+2zx
=z(z−1)+2xy
is finite. Find all such triples.-/

theorem algebra_321203: {(a, b, c): ℂ × ℂ × ℂ | ∃ x y z, a = x - y ∧ b = y - z ∧ c = z - x ∧
  x * (x - 1) + 2 * y * z = y * (y - 1) + 2 * z * x ∧
  y * (y - 1) + 2 * z * x = z * (z - 1) + 2 * x * y} = {(0, 0, 0), (0, -1, 1), (1, 0, -1), (-1, 1, 0)} := by

    ext ⟨a, b, c⟩
    simp only [Set.mem_setOf_eq]
    constructor

    -- the forward direction
    .
      intro h
      obtain ⟨x, y, z, ha, hb, hc, h1, h2⟩ := h
      have h3: z * (z - 1) + 2 * x * y = x * (x - 1) + 2 * y * z := by
        rw [← h2, ← h1]
      simp

      -- use lemma to factor the equation
      replace h1:= lemma_1 x y z h1
      replace h2:= lemma_1 y z x h2
      replace h3:= lemma_1 z x y h3
      rw [← ha, ← hb, ← hc] at h1 h2 h3
      clear ha hb hc
      simp at h1 h2 h3
      rcases h1 with h1 | h1

      -- case 1: a = 0
      .
        simp [h1] at *
        rcases h2 with h2 | h2
        .
          simp [h2] at *
          simp [h3]
        .
          rcases h3 with h3 | h3
          .
            simp [h3] at *
          .
            right
            replace h3: b = -1 := by
              rw [show -1 = -b - 1 + b by ring]
              simp [h3]
            simp [h3]
            replace h2: c = 1 := by
              rw [show 1 = c - (c - 1) by ring]
              simp [h2]
            simp [h2]
        
      -- case 2: a = 1
      .
        rcases h2 with h2 | h2
        .
          simp [h2] at *
          replace h1: c = -1 := by
            rw [show -1 = -c - 1 + c by ring]
            simp [h1]
          simp [h1]
          rcases h3 with h3 | h3
          .
            simp [h3] at h1
          .
            replace h3: a = 1 := by
              rw [show 1 = a - (a - 1) by ring]
              simp [h3]
            simp [h3]
        .
          rcases h3 with h3 | h3
          .
            simp [h3] at *
            replace h1: b = 1 := by
              rw [show 1 = b - (b - 1) by ring]
              simp [h1]
            simp [h1] at *
            rw [show -1 = -a - 1 + a by ring]
            simp [h2]
          .
            have f: (b - c - 1) + (c - a - 1) + (a - b - 1) = 0 := by
              rw [h1, h2, h3]
              norm_num
            rw [show (b - c - 1) + (c - a - 1) + (a - b - 1) = -3 by ring] at f
            norm_num at f


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h | h
      .
        use 0
        use 0
        use 0
        simp [h]
      .
        use 0
        use 0
        use 1
        simp [h]
      .
        use 1
        use 0
        use 0
        simp [h]
      .
        use 0
        use 1
        use 0
        simp [h]