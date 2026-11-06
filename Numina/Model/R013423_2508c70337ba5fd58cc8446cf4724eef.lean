import Mathlib

theorem algebra_245845 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x, f (x + 5) = f x)
    (hf1 : f (1 / 3) = 1) :
    f (16 / 3) + f (29 / 3) + f 12 + f (-7) = 0 := by
  -- Compute f(16/3) = f(1/3 + 5) = f(1/3) = 1
  have h1 : f (16 / 3) = 1 := by 
    have h2 : f (1 / 3 + 5) = f (1 / 3) := by 
      specialize hf (1 / 3)
      simpa using hf 
    have h3 : (1 / 3 : ℝ) + 5 = (16 / 3 : ℝ) := by 
      linarith 
    rw [h3] at h2 
    linarith [hf1, h2]
  -- Compute f(29/3):
  -- $29/3 = -1/3 + 5 \cdot 2$
  -- So $f(29/3) = f(-1/3 + 10) = f(-1/3) = -f(1/3) = -1$ using the periodicity and odd property
  have h4 : f (29 / 3) = -1 := by
    have h41 : f (29 / 3) = f (14 / 3) := by 
      have h42 : f (14 / 3) = f (29 / 3) := by
        have h43 : f (14 / 3 + 5) = f (14 / 3) := by
          specialize hf (14 / 3)
          simpa using hf 
        have h44 : (14 / 3 + 5 : ℝ) = (29 / 3 : ℝ) := by
          linarith 
        rw [h44] at h43 
        linarith 
      linarith 
    have h43 : f (14 / 3) = f (-1 / 3) := by 
      have h44 : f (-1 / 3) = f (14 / 3) := by
        have h45 : f ((-1 / 3 : ℝ) + 5) = f (-1 / 3) := by 
          specialize hf (-1 / 3)
          simpa using hf 
        have h46 : (-1 / 3 + 5 : ℝ) = (14 / 3 : ℝ) := by 
          linarith 
        rw [h46] at h45 
        linarith 
      linarith 
    have h46 : f (-1 / 3) = -1 := by 
      specialize hodd (1 / 3)
      have h47 : f (- (1 / 3 : ℝ)) = - f (1 / 3 : ℝ) := by 
        simpa using hodd 
      have h48 : f (-1 / 3 : ℝ) = -f (1 / 3 : ℝ) := by 
        ring_nf at h47 ⊢ 
        linarith 
      rw [h48] 
      linarith [hf1]
    rw [h41, h43, h46]
  -- Compute f(12) = f(2)
  have h9 : f (12 : ℝ) = f (2 : ℝ) := by 
    have h11 : f (12 : ℝ) = f (7 : ℝ) := by 
      have h12 : f (7 : ℝ) = f (12 : ℝ) := by 
        have h13 : f (7 : ℝ) = f (12 : ℝ) := by 
          have h14 : f ((7 : ℝ) + 5) = f (7 : ℝ) := by 
            specialize hf (7 : ℝ)
            simpa using hf 
          have h15 : (7 + 5 : ℝ) = (12 : ℝ) := by 
            linarith 
          rw [h15] at h14 
          linarith 
        linarith 
      linarith 
    have h10 : f (7 : ℝ) = f (2 : ℝ) := by 
      have h11 : f (7 : ℝ) = f (2 : ℝ) := by 
        have h12 : f ((2 : ℝ) + 5) = f (2 : ℝ) := by 
          specialize hf (2 : ℝ)
          simpa using hf 
        have h13 : (2 + 5 : ℝ) = (7 : ℝ) := by 
          linarith 
        rw [h13] at h12 
        linarith 
      linarith 
    linarith 
  -- Compute f(-7) = -f(7) = -f(2)
  have h101 : f (-7 : ℝ) = - f (7 : ℝ) := by 
    specialize hodd (7 : ℝ)
    have h111 : f (- (7 : ℝ)) = - f (7 : ℝ) := by 
      simpa using hodd 
    have h112 : f (-7 : ℝ) = f (- (7 : ℝ)) := by 
      ring_nf 
    linarith [h111, h112] 
  -- f(7) = f(2)
  have h113 : f (7 : ℝ) = f (2 : ℝ) := by 
    have h114 : f ((2 : ℝ) + 5) = f (2 : ℝ) := by 
      specialize hf (2 : ℝ)
      simpa using hf 
    have h115 : (2 + 5 : ℝ) = (7 : ℝ) := by 
      linarith 
    rw [h115] at h114 
    linarith 
  -- Sum them all up:
  -- f(16/3) = 1
  -- f(29/3) = -1
  -- f(12) = f(2)
  -- f(-7) = -f(2)
  -- So total sum is 1 - 1 + (f(2)) + (-f(2)) = 0
  rw [h1, h4, h9, h101, h113]
  linarith