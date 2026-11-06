import Mathlib

theorem algebra_161020 {f : ℝ → ℝ} 
    (h1 : ∀ x, f (2 - x) = f (2 + x)) 
    (h2 : ∀ x, f (7 - x) = f (7 + x))
    (h3 : f 0 = 0) :
    ∃ s : Finset ℝ, s.card ≥ 13 ∧ ∀ x ∈ s, f x = 0 ∧ x ∈ Set.Icc (-30) 30 ∧
    ∃ c : ℝ, Function.Periodic f c ∧ c = 10 := by
  -- Show that $f$ is symmetric about $x=2$ and $x=7$, implying a period of 10.
  have h4 : ∀ x, f x = f (4 - x) := by 
    intro x 
    have h5 := h1 (2 - x)
    rw [show 2 - (2 - x) = x by ring, show 2 + (2 - x) = (4 - x : ℝ) by ring] at h5 
    linarith 
  have h5 : ∀ x, f x = f (14 - x) := by 
    intro x
    have h6 := h2 (7 - x)
    rw [show 7 - (7 - x) = x by ring, show 7 + (7 - x) = (14 - x : ℝ) by ring] at h6 
    linarith
  have h6 : ∀ x, f (x + 10) = f x := by 
    intro x 
    have eq1 : f x = f (4 - x) := h4 x
    have eq2 : f (4 - x) = f (10 + x) := by 
      have : f (4 - x) = f (14 - (4 - x)) := h5 (4 - x)
      have h7 : 14 - (4 - x) = (10 + x) := by ring
      rw [h7] at this 
      linarith 
    have eq3 : f (x + 10) = f (10 + x) := by 
      rw [show x + 10 = 10 + x by ring]
      all_goals linarith 
    linarith [eq1, eq2, eq3]
  
  -- Show that $f(4) = 0$ using $f(0) = 0$ and symmetry.
  have h40 : f 4 = 0 := by 
    specialize h1 2
    norm_num at h1 
    linarith [h3]

  -- Construct the set of 13 zeros in $[-30, 30]$ using $f(0) = 0$ and $f(4) = 0$ with periodicity.
  use { -30, -26, -20, -16, -10, -6, 0, 4, 10, 14, 20, 24, 30 }
  constructor
  · -- Show the cardinality is at least 13
    norm_num
  · -- Show all elements satisfy the conditions
    intro x hx
    have hx1 : x = -30 ∨ x = -26 ∨ x = -20 ∨ x = -16 ∨ x = -10 ∨ x = -6 ∨ x = (0 : ℝ) ∨ x = 4 ∨ x = 10 ∨ x = 14 ∨ x = 20 ∨ x = 24 ∨ x = 30 := by
      norm_num at hx ⊢
      <;> tauto 
    rcases hx1 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · -- x = -30
      constructor
      · -- Show f(-30) = 0
        have h7 : f (-30) = f 0 := by 
          calc 
            f (-30) = f (-30 + 10) := by rw [h6 (-30)]
            _ = f (-20) := by ring_nf
            _ = f (-20 + 10) := by rw [h6 (-20)]
            _ = f (-10) := by ring_nf 
            _ = f (-10 + 10) := by rw [h6 (-10)]
            _ = f 0 := by ring_nf 
        rw [h3] at h7 
        linarith 
      constructor 
      · -- Show -30 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = -26
      constructor
      · -- Show f(-26) = 0
        have h7 : f (-26) = f 4 := by 
          calc 
            f (-26) = f (-26 + 10) := by rw [h6 (-26)]
            _ = f (-16) := by ring_nf
            _ = f (-16 + 10) := by rw [h6 (-16)]
            _ = f (-6) := by ring_nf
            _ = f (-6 + 10) := by rw [h6 (-6)]
            _ = f 4 := by ring_nf
        rw [h40] at h7 
        linarith 
      constructor 
      · -- Show -26 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = -20
      constructor
      · -- Show f(-20) = 0
        have h7 : f (-20) = f 0 := by 
          calc 
            f (-20) = f (-20 + 10) := by rw [h6 (-20)]
            _ = f (-10) := by ring_nf 
            _ = f (-10 + 10) := by rw [h6 (-10)]
            _ = f 0 := by ring_nf 
        rw [h3] at h7 
        linarith 
      constructor 
      · -- Show -20 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = -16
      constructor
      · -- Show f(-16) = 0
        have h7 : f (-16) = f 4 := by 
          calc 
            f (-16) = f (-16 + 10) := by rw [h6 (-16)]
            _ = f (-6) := by ring_nf
            _ = f (-6 + 10) := by rw [h6 (-6)]
            _ = f 4 := by ring_nf
        rw [h40] at h7 
        linarith 
      constructor 
      · -- Show -16 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = -10
      constructor
      · -- Show f(-10) = 0
        have h7 : f (-10) = f 0 := by 
          calc 
            f (-10) = f (-10 + 10) := by rw [h6 (-10)]
            _ = f 0 := by ring_nf 
        rw [h3] at h7 
        linarith 
      constructor 
      · -- Show -10 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = -6
      constructor
      · -- Show f(-6) = 0
        have h7 : f (-6) = f 4 := by 
          calc 
            f (-6) = f (-6 + 10) := by rw [h6 (-6)]
            _ = f 4 := by ring_nf
        rw [h40] at h7 
        linarith 
      constructor 
      · -- Show -6 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = 0
      constructor
      · -- Show f(0) = 0
        exact h3 
      constructor 
      · -- Show 0 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = 4
      constructor
      · -- Show f(4) = 0
        exact h40 
      constructor 
      · -- Show 4 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = 10
      constructor
      · -- Show f(10) = 0
        have h7 : f 10 = f 0 := by 
          calc 
            f 10 = f (0 + 10) := by ring_nf 
            _ = f 0 := by rw [h6 0]
        rw [h3] at h7 
        linarith 
      constructor 
      · -- Show 10 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = 14
      constructor
      · -- Show f(14) = 0
        have h7 : f 14 = f 4 := by 
          calc 
            f 14 = f (4 + 10) := by ring_nf 
            _ = f 4 := by rw [h6 4]
        rw [h40] at h7 
        linarith 
      constructor 
      · -- Show 14 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = 20
      constructor
      · -- Show f(20) = 0
        have h7 : f 20 = f 0 := by 
          calc 
            f 20 = f (10 + 10) := by ring_nf 
            _ = f 10 := by rw [h6 10]
            _ = f (0 + 10) := by ring_nf 
            _ = f 0 := by rw [h6 0]
        rw [h3] at h7 
        linarith 
      constructor 
      · -- Show 20 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = 24
      constructor
      · -- Show f(24) = 0
        have h7 : f 24 = f 4 := by 
          calc 
            f 24 = f (14 + 10) := by ring_nf 
            _ = f 14 := by rw [h6 14]
            _ = f (4 + 10) := by ring_nf 
            _ = f 4 := by rw [h6 4]
        rw [h40] at h7 
        linarith 
      constructor 
      · -- Show 24 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }
    · -- x = 30
      constructor
      · -- Show f(30) = 0
        have h7 : f 30 = f 0 := by 
          calc 
            f 30 = f (20 + 10) := by ring_nf 
            _ = f 20 := by rw [h6 20]
            _ = f (10 + 10) := by ring_nf 
            _ = f 10 := by rw [h6 10]
            _ = f (0 + 10) := by ring_nf
            _ = f 0 := by rw [h6 0]
        rw [h3] at h7 
        linarith 
      constructor 
      · -- Show 30 ∈ [-30, 30]
        norm_num 
      · -- Show there exists a period c = 10
        use 10 
        all_goals 
          try { 
            tauto 
          } 
          try { 
            intro x 
            simpa using h6 x 
          }