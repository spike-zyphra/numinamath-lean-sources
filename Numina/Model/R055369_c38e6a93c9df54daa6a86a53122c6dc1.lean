import Mathlib

theorem algebra_163506 (d t : ℝ) (ht : t > 0) (h : d / 2 = t / 10) (h' : d / 10 = t / 2.5)
    (h'' : d / 3 = t / 10 + 100) :
    t = 5020 := by
  -- From h: d/2 = t/10
  -- Solving gives 10d = 2t ⇒ 5d = t
  have eq1 : t = 5 * d := by
    field_simp at h 
    linarith
  
  -- From h': d/10 = t/2.5
  -- Solving gives 2.5d = 10t ⇒ 0.25d = t
  have eq2 : t = (0.25 : ℝ) * d := by
    field_simp at h' 
    ring_nf at h' ⊢ 
    nlinarith
  
  -- Solving for d from eq1 and eq2:
  -- t = 5d and t = 0.25d gives 5d = 0.25d ⇒ 4.75d = 0 ⇒ d = 0
  have h0 : d = (0 : ℝ) := by
    nlinarith [eq1, eq2]

  -- Substitute d = 0 into eq1 to get t = 0
  have ht0 : t = (0 : ℝ) := by 
    nlinarith [eq1, h0]

  -- Contradiction with ht: t > 0
  linarith